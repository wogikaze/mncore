"""Command line: compile a Python kernel with a tensor contract to VSM.

    python -m mncompile kernel.py --contract contract.json --output out/

The contract lists the input and output tensors as the problem statements do:

    {"inputs":  [{"name": "A", "dtype": "Float", "memory": "$lm[0:16]",
                  "layout": "(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])",
                  "low": -512, "high": 512}],
     "outputs": [{"name": "C", "dtype": "Float", "memory": "$ln[0:16]",
                  "layout": "(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))",
                  "atol": 1e-5}]}

`kernel(...)` receives the inputs (nested lists) in contract order and returns
the outputs. The compiler writes kernel.vsm and report.json to the output
directory.
"""

import argparse
import json
from pathlib import Path

from .compiler import compile_program
from .errors import CompileError
from .layout import Contract
from .memlimit import limit_process


def main() -> None:
    parser = argparse.ArgumentParser(description="Compile a Python kernel to MN-Core 2 VSM")
    parser.add_argument("source", type=Path, help="Python file defining kernel(...)")
    parser.add_argument("--contract", type=Path, required=True, help="JSON tensor contract")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--backend", choices=["native", "official"], default="native",
                        help="simulator used to verify candidates (the official emulator is always used for opcodes the native one does not model)")
    parser.add_argument("--tries", type=int, default=4, help="schedules tried per candidate")
    parser.add_argument("-v", "--verbose", action="store_true")
    parser.add_argument("--memory-fraction", type=float, default=0.6,
                        help="cap the compiler at this fraction of physical memory (MemoryError instead of exhausting the machine)")
    args = parser.parse_args()
    limit_process(args.memory_fraction)
    try:
        contract = Contract.from_json(json.loads(args.contract.read_text()))
        compiled = compile_program(
            args.source.read_text(encoding="utf-8"),
            contract,
            tries=args.tries,
            backend=args.backend,
            log=print if args.verbose else None,
        )
        compiled.write(args.output)
    except (CompileError, OSError) as exc:
        parser.exit(1, f"compile error: {exc}\n")
    print(json.dumps({k: compiled.report[k] for k in ("lines", "strategy", "candidates")}, indent=2))


if __name__ == "__main__":
    main()
