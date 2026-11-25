#!/bin/bash
# Compiles the workloads of compile_workloads.py with MLSDK 0.9 in the SDK image.
# Usage: run_compile.sh OUT_DIR   (OUT_DIR must be under /home)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$(realpath -m "$1")
mkdir -p "$out"
docker run --rm -v /home:/home mncore-sdk-minimal:0.9 bash -c \
  "source /opt/pfn/pfcomp/codegen/build/codegen_pythonpath.sh && python3 $here/compile_workloads.py $out" \
  2>&1 | grep -E "^compiled|Error|error:" || true
for d in "$out"/*/; do
  [ -f "$d/model.vsm.zst" ] && zstd -qdcf "$d/model.vsm.zst" > "$out/$(basename "$d").vsm"
done
ls "$out"/*.vsm
