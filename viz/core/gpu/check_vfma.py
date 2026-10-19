#!/usr/bin/env python3
"""Checks the CUDA f32 vfma kernel against the CPU simulator's vectors.

Generate the vectors first:

    cargo run --release --bin vfma_vectors -- 1000000 target/vfma_vectors.bin

Then run this script from viz/core. It needs the WSL driver (libcuda.so.1) and the
NVRTC library shipped with the PyTorch CUDA wheels. Override the paths with
CUDA_LIB and NVRTC_LIB.
"""

from __future__ import annotations

import argparse
import ctypes
import ctypes.util
import glob
import os
import struct
import sys
import time

try:
    import nvidia
except ImportError:
    nvidia = None


def nvrtc_path() -> str:
    if os.environ.get("NVRTC_LIB"):
        return os.environ["NVRTC_LIB"]
    if nvidia is not None:
        site = os.path.dirname(os.path.dirname(nvidia.__file__))
        hits = glob.glob(os.path.join(site, "nvidia", "cuda_nvrtc", "lib", "libnvrtc.so*"))
        if hits:
            return hits[0]
    raise SystemExit("libnvrtc not found; set NVRTC_LIB")


def cuda_path() -> str:
    if os.environ.get("CUDA_LIB"):
        return os.environ["CUDA_LIB"]
    for path in ("/usr/lib/wsl/lib/libcuda.so.1", "/usr/lib/x86_64-linux-gnu/libcuda.so.1"):
        if os.path.exists(path):
            return path
    found = ctypes.util.find_library("cuda")
    if not found:
        raise SystemExit("libcuda not found; set CUDA_LIB")
    return found


class Driver:
    def __init__(self) -> None:
        self.cuda = ctypes.CDLL(cuda_path())
        self.cuda.cuGetErrorString.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_char_p)]
        self.cu(self.cuda.cuInit(0), "cuInit")
        device = ctypes.c_int()
        self.cu(self.cuda.cuDeviceGet(ctypes.byref(device), 0), "cuDeviceGet")
        context = ctypes.c_void_p()
        self.cu(self.cuda.cuCtxCreate_v2(ctypes.byref(context), 0, device), "cuCtxCreate")
        self.context = context

    def cu(self, code: int, what: str) -> int:
        if code:
            text = ctypes.c_char_p()
            self.cuda.cuGetErrorString(code, ctypes.byref(text))
            message = text.value.decode() if text.value else str(code)
            raise RuntimeError(f"{what}: {message}")
        return code

    def module(self, ptx: ctypes.Array) -> ctypes.c_void_p:
        module = ctypes.c_void_p()
        self.cu(self.cuda.cuModuleLoadDataEx(ctypes.byref(module), ptx, 0, None, None), "module")
        return module

    def function(self, module: ctypes.c_void_p, name: bytes) -> ctypes.c_void_p:
        function = ctypes.c_void_p()
        self.cu(self.cuda.cuModuleGetFunction(ctypes.byref(function), module, name), "function")
        return function

    def alloc(self, size: int) -> ctypes.c_void_p:
        pointer = ctypes.c_void_p()
        self.cu(self.cuda.cuMemAlloc_v2(ctypes.byref(pointer), size), "alloc")
        return pointer

    def upload(self, pointer: ctypes.c_void_p, data, size: int) -> None:
        self.cu(self.cuda.cuMemcpyHtoD_v2(pointer, data, size), "upload")

    def download(self, data, pointer: ctypes.c_void_p, size: int) -> None:
        self.cu(self.cuda.cuMemcpyDtoH_v2(data, pointer, size), "download")

    def launch(self, function, grid: int, block: int, args) -> None:
        self.cu(
            self.cuda.cuLaunchKernel(function, grid, 1, 1, block, 1, 1, 0, None, args, None),
            "launch",
        )

    def sync(self) -> None:
        self.cu(self.cuda.cuCtxSynchronize(), "sync")


def compile_ptx(source: bytes) -> ctypes.Array:
    nvrtc = ctypes.CDLL(nvrtc_path())
    program = ctypes.c_void_p()
    nvrtc.nvrtcCreateProgram(ctypes.byref(program), source, b"vfma.cu", 0, None, None)
    options = (ctypes.c_char_p * 2)(b"--gpu-architecture=compute_86", b"--device-int128")
    result = nvrtc.nvrtcCompileProgram(program, 2, options)
    if result:
        size = ctypes.c_size_t()
        nvrtc.nvrtcGetProgramLogSize(program, ctypes.byref(size))
        log = ctypes.create_string_buffer(size.value)
        nvrtc.nvrtcGetProgramLog(program, log)
        raise SystemExit(log.value.decode(errors="replace"))
    size = ctypes.c_size_t()
    nvrtc.nvrtcGetPTXSize(program, ctypes.byref(size))
    ptx = ctypes.create_string_buffer(size.value)
    nvrtc.nvrtcGetPTX(program, ptx)
    return ptx


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("vectors", nargs="?", default="target/vfma_vectors.bin")
    parser.add_argument("--kernel", default=os.path.join(os.path.dirname(__file__), "vfma_kernel.cu"))
    parser.add_argument("--lines", type=int, default=3558)
    parser.add_argument("--line-values", type=int, default=32768)
    args = parser.parse_args()

    raw = open(args.vectors, "rb").read()
    count = len(raw) // 16
    if count == 0:
        raise SystemExit("run vfma_vectors first")
    a = (ctypes.c_uint * count)()
    b = (ctypes.c_uint * count)()
    c = (ctypes.c_uint * count)()
    expected = (ctypes.c_uint * count)()
    for i in range(count):
        a[i], b[i], c[i], expected[i] = struct.unpack_from("<IIII", raw, i * 16)

    ptx = compile_ptx(open(args.kernel, "rb").read())
    driver = Driver()
    function = driver.function(driver.module(ptx), b"vfma_f32")
    size = count * 4
    da, db, dc = driver.alloc(size), driver.alloc(size), driver.alloc(size)
    out = driver.alloc(size)
    driver.upload(da, a, size)
    driver.upload(db, b, size)
    driver.upload(dc, c, size)
    n = ctypes.c_int(count)
    kernel_args = (ctypes.c_void_p * 5)(
        ctypes.cast(ctypes.byref(da), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(db), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(dc), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(out), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(n), ctypes.c_void_p),
    )
    grid = (count + 255) // 256
    driver.launch(function, grid, 256, kernel_args)
    driver.sync()
    result = (ctypes.c_uint * count)()
    driver.download(result, out, size)
    mismatches = [i for i in range(count) if result[i] != expected[i]]
    print(f"checked {count} vectors, {len(mismatches)} mismatches")
    if mismatches:
        i = mismatches[0]
        print(
            f"first: a={a[i]:08x} b={b[i]:08x} c={c[i]:08x} "
            f"gpu={result[i]:08x} cpu={expected[i]:08x}"
        )
        return 1

    for _ in range(3):
        start = time.perf_counter()
        driver.launch(function, grid, 256, kernel_args)
        driver.sync()
        elapsed = time.perf_counter() - start
        print(f"batch: {elapsed * 1e3:.2f} ms, {count / elapsed / 1e6:.1f} Mvfma/s")

    line_count = min(args.line_values, count)
    line_size = line_count * 4
    la, lb, lc = driver.alloc(line_size), driver.alloc(line_size), driver.alloc(line_size)
    lo = driver.alloc(line_size)
    driver.upload(la, a, line_size)
    driver.upload(lb, b, line_size)
    driver.upload(lc, c, line_size)
    ln = ctypes.c_int(line_count)
    line_args = (ctypes.c_void_p * 5)(
        ctypes.cast(ctypes.byref(la), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(lb), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(lc), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(lo), ctypes.c_void_p),
        ctypes.cast(ctypes.byref(ln), ctypes.c_void_p),
    )
    line_grid = (line_count + 255) // 256
    for _ in range(2):
        start = time.perf_counter()
        for _ in range(args.lines):
            driver.launch(function, line_grid, 256, line_args)
        driver.sync()
        elapsed = time.perf_counter() - start
        print(
            f"{args.lines} line launches: {elapsed * 1e3:.2f} ms, "
            f"{elapsed / args.lines * 1e6:.2f} us/line, "
            f"{args.lines * line_count / elapsed / 1e6:.1f} Mvfma/s"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
