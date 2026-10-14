import argparse
import json
from pathlib import Path

from .compiler import CompileError, compile_source
from .frontend import compile_program
from .generators import GlobalTensor
from .maps import Tensor


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compile restricted Python to error-budgeted MN-Core VSM"
    )
    parser.add_argument("source", type=Path)
    parser.add_argument("--domain", type=float, nargs=2, metavar=("LOW", "HIGH"))
    parser.add_argument("--atol", type=float)
    parser.add_argument(
        "--bindings",
        type=Path,
        help="JSON input/output dtype, range and physical layout contract",
    )
    parser.add_argument(
        "--words", type=int, default=8, help="Float elements per PE (multiple of 8)"
    )
    parser.add_argument("--opt", default="opt", help="LLVM opt executable")
    parser.add_argument(
        "--assembler",
        help="Official assemble3 executable; validate and measure each candidate",
    )
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.bindings:
            if args.domain:
                raise CompileError("Use either --bindings or --domain")
            contract = json.loads(args.bindings.read_text())
            output_type = GlobalTensor if "group" in contract["output"] else Tensor
            compiled = compile_program(
                args.source.read_text(),
                inputs={
                    name: Tensor(**spec) for name, spec in contract["inputs"].items()
                },
                output=output_type(**contract["output"]),
                row_partition=contract.get("row_partition", "local"),
                atol=args.atol if args.atol is not None else contract.get("atol"),
                opt=args.opt,
                assembler=args.assembler,
            )
        else:
            if not args.domain or args.atol is None:
                raise CompileError(
                    "Scalar polynomial compilation requires --domain and --atol; array programs require --bindings"
                )
            compiled = compile_source(
                args.source.read_text(encoding="utf-8"),
                domain=tuple(args.domain),
                atol=args.atol,
                words=args.words,
                opt=args.opt,
                assembler=args.assembler,
            )
        compiled.write(args.output)
    except (CompileError, OSError) as exc:
        parser.exit(1, f"compile error: {exc}\n")
    print(
        json.dumps(
            {
                key: compiled.report[key]
                for key in (
                    "chosen",
                    "chosen_lowering",
                    "lines",
                    "error_bound",
                    "cost_kind",
                )
                if key in compiled.report
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
