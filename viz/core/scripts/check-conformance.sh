#!/usr/bin/env bash
# Every conformance surface in one command. Any mismatch anywhere fails the run.
#
#   ./scripts/check-conformance.sh          # CPU vs official emulator + cargo test
#   ./scripts/check-conformance.sh --gpu    # adds the four GPU harnesses and the whole-program run
#
# The CPU-vs-official sweep is the guard that matters most: it covers every
# checked-in problem and needs no GPU, so it also runs on CI. The GPU part is
# opt-in because it needs the WSL2 CUDA driver (`/dev/dxg`).
set -uo pipefail

cd "$(dirname "$0")/.."

with_gpu=0
for arg in "$@"; do
    case "$arg" in
        --gpu) with_gpu=1 ;;
        -h|--help) sed -n '2,9p' "$0"; exit 0 ;;
        *) echo "unknown argument: $arg" >&2; exit 2 ;;
    esac
done

# The worktree used by `git worktree add` has no judge/ checkout; point at the
# shared emulator binaries instead of silently skipping the whole sweep.
if [ -z "${MNCORE_EMU_DIR:-}" ] && [ ! -x "../../judge/judge-py/mncore2_emuenv/gpfn3_package_main" ]; then
    root=$(git rev-parse --show-toplevel)
    if [ -x "$root/judge/judge-py/mncore2_emuenv/gpfn3_package_main" ]; then
        export MNCORE_EMU_DIR="$root/judge/judge-py/mncore2_emuenv"
    fi
fi
if [ ! -x "${MNCORE_EMU_DIR:-../../judge/judge-py/mncore2_emuenv}/gpfn3_package_main" ]; then
    echo "error: the official emulator is missing; run setup_judge.sh or set MNCORE_EMU_DIR" >&2
    exit 2
fi

fail=0
step() {
    echo
    echo "=== $* ==="
}

step "build"
cargo build --release --offline --bins || exit 1

step "cargo test"
cargo test --release --offline || fail=1

# Every problem and every challenge solution against the official emulator.
step "CPU vs official emulator: every problem"
cargo test --release --offline --test problem_conformance -- --ignored --nocapture || fail=1

if [ "$with_gpu" = 1 ]; then
    # Full state comparison per instruction family. These are the only surfaces
    # that exercise the kernels directly.
    step "GPU: ALU, L1BM, MAU and memory conformance"
    ./target/release/gpu_alu_conformance || fail=1
    ./target/release/gpu_l1_conformance 3 || fail=1
    ./target/release/gpu_mau_conformance || fail=1
    ./target/release/gpu_mem_conformance || fail=1

    step "GPU: whole mnist_train_step program"
    ./target/release/gpu_run_program benchmarks/mnist_train_step.vsm || fail=1
fi

echo
if [ "$fail" = 0 ]; then
    echo "PASS: CPU, GPU and the official emulator agree on every checked surface"
else
    echo "FAIL: see the mismatches above"
fi
exit "$fail"
