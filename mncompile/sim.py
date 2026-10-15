"""Clients for the native simulator server and the official tools."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import threading
from dataclasses import dataclass
from pathlib import Path

from .errors import CompileError
from .memlimit import lift_for_child

ROOT = Path(__file__).resolve().parent.parent
NATIVE_DIR = Path(__file__).resolve().parent / "native"
NATIVE_BIN = NATIVE_DIR / "target" / "release" / "mncompile-native"
EMU_DIR = Path(os.environ.get("MNCORE_EMU_DIR", ROOT / "judge" / "judge-py" / "mncore2_emuenv"))


def ensure_native():
    if NATIVE_BIN.exists():
        return NATIVE_BIN
    if shutil.which("cargo") is None:
        raise CompileError("Building the simulator needs cargo")
    subprocess.run(["cargo", "build", "--release"], cwd=NATIVE_DIR, check=True, capture_output=True, preexec_fn=lift_for_child)
    return NATIVE_BIN


@dataclass
class RunResult:
    words: int | None
    error: str | None
    part: str | None
    line: int | None
    dump: dict  # (mem, pe_path, addr) -> int

    @property
    def ok(self):
        return self.error is None


class Simulator:
    """A persistent native simulator process (thread-safe via a lock)."""

    def __init__(self):
        self.proc = subprocess.Popen(
            [str(ensure_native())],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
            bufsize=1,
            preexec_fn=lift_for_child,
        )
        self.lock = threading.Lock()
        self.registered = set()

    def _request(self, payload):
        with self.lock:
            self.proc.stdin.write(json.dumps(payload) + "\n")
            self.proc.stdin.flush()
            line = self.proc.stdout.readline()
        if not line:
            raise CompileError("simulator process died")
        return json.loads(line)

    def register(self, key: str, text: str):
        if key in self.registered:
            return
        response = self._request({"register": key, "text": text})
        if "error" in response:
            raise CompileError(f"simulator rejected {key}: {response['error']}")
        self.registered.add(key)

    def run(self, program: str, prefix_key: str | None = None, suffix_key: str | None = None, prefix: str = "", suffix: str = "") -> RunResult:
        payload = {"program": program}
        if prefix_key:
            payload["prefix_id"] = prefix_key
        else:
            payload["prefix"] = prefix
        if suffix_key:
            payload["suffix_id"] = suffix_key
        else:
            payload["suffix"] = suffix
        r = self._request(payload)
        dump = {}
        for mem, pe, addr, value in r.get("dump", []):
            dump[(mem, pe, addr)] = int(value, 16)
        return RunResult(r.get("words"), r.get("error"), r.get("part"), r.get("line"), dump)

    def close(self):
        try:
            self.proc.stdin.close()
            self.proc.wait(timeout=5)
        except Exception:
            self.proc.kill()


_pool: list[Simulator] = []
_pool_lock = threading.Lock()


def simulator() -> Simulator:
    with _pool_lock:
        if not _pool:
            _pool.append(Simulator())
        return _pool[0]


@dataclass
class AssemblyResult:
    ok: bool
    words: int
    error: str
    code: str


class Assembler:
    def __init__(self, path: str | Path | None = None):
        self.path = str(path or EMU_DIR / "assemble3")
        if not Path(self.path).exists():
            raise CompileError(f"Official assembler not found at {self.path}")
        self.cache: dict[str, AssemblyResult] = {}

    def assemble(self, text: str) -> AssemblyResult:
        hit = self.cache.get(text)
        if hit is not None:
            return hit
        p = subprocess.run([self.path, "--instruction-mode", "flat"], input=text, text=True, capture_output=True, preexec_fn=lift_for_child)
        words = sum(1 for line in p.stdout.splitlines() if line.startswith(("j ", "m ")))
        err = p.stderr.strip()
        result = AssemblyResult(p.returncode == 0, words, err, p.stdout)
        self.cache[text] = result
        return result


_assembler: Assembler | None = None


def assembler() -> Assembler:
    global _assembler
    if _assembler is None:
        _assembler = Assembler()
    return _assembler


_DEBUG = None


def _parse_debug(text: str) -> dict:
    """Parse emulator `d get` output into {(mem, pe_path, addr): long word}."""
    import re

    out = {}
    for line in text.splitlines():
        m = re.match(r"DEBUG-(\w+)\(([^,]+),(\d+)\):(.*)", line)
        if not m:
            continue
        mem, pe, addr, rest = m[1], m[2], int(m[3]), m[4]
        if "v:0x" in rest:
            hexes = re.findall(r"v:0x([0-9a-fA-F]+)", rest)
        else:
            hexes = re.findall(r"\(0x([0-9a-fA-F]+)\)", rest)
            if not hexes:
                inner = re.search(r"\) \((0x[^)]*)\)", rest)
                hexes = [h[2:] for h in inner[1].split(", ")] if inner else []
        if not hexes:
            continue
        if len(hexes) == 1:
            out[(mem, pe, addr)] = int(hexes[0], 16)
        else:
            # typed dumps print lanes separately; reassemble MSB first
            width = 64 // len(hexes)
            word = 0
            for h in hexes:
                word = (word << width) | int(h, 16)
            out[(mem, pe, addr)] = word
    return out


def official_run(program: str, prefix: str, suffix: str) -> RunResult:
    """Assemble with the official assembler and run the official emulator."""
    asm = assembler().assemble(program)
    if not asm.ok:
        return RunResult(None, "assembler: " + asm.error.splitlines()[0] if asm.error else "assembler failed", "program", None, {})
    body = "".join(line + "\n" for line in asm.code.splitlines() if line.startswith(("j ", "m ")))
    text = prefix + body + suffix
    p = subprocess.run(
        [str(EMU_DIR / "gpfn3_package_main"), "--offchip-memory-init", "zero"],
        input=text,
        text=True,
        capture_output=True,
        env={**os.environ, "OMP_THREAD_LIMIT": "1"},
        preexec_fn=lift_for_child,
    )
    if p.returncode != 0:
        return RunResult(asm.words, "emulator: " + (p.stderr.strip().splitlines() or ["failed"])[-1][:300], "program", None, {})
    return RunResult(asm.words, None, None, None, _parse_debug(p.stderr + p.stdout))
