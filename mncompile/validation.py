"""Run all compiler tests and save a machine-readable, non-proof validation record."""

import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path


def implementation_digest(root):
    digest = hashlib.sha256()
    for path in sorted(root.rglob("*.py")):
        digest.update(str(path.relative_to(root)).encode() + b"\0" + path.read_bytes())
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assembler", required=True)
    parser.add_argument("--emulator", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    env = dict(
        os.environ, MNCORE_ASSEMBLER=args.assembler, MNCORE_EMULATOR=args.emulator
    )
    program = (
        "import json,unittest\n"
        'suite=unittest.defaultTestLoader.discover("mncompile",top_level_dir=".")\n'
        "result=unittest.TextTestRunner(verbosity=2).run(suite)\n"
        'print(json.dumps({"tests_run":result.testsRun,"failures":len(result.failures),"errors":len(result.errors),"skipped":len(result.skipped),"successful":result.wasSuccessful()}))\n'
        "raise SystemExit(not result.wasSuccessful())\n"
    )
    result = subprocess.run(
        [sys.executable, "-c", program],
        cwd=root.parent,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    sys.stderr.write(result.stderr)
    if not result.stdout.strip():
        raise SystemExit(result.returncode or 1)
    report = json.loads(result.stdout.splitlines()[-1])
    report.update(
        implementation_sha256=implementation_digest(root),
        command="python -m mncompile.validation --assembler PATH --emulator PATH --output PATH",
        scope="Independent domain/boundary/basis/exhaustive-lane tests plus official emulator; not a formal whole-machine proof",
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
