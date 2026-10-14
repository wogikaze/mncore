"""Source-driven entry point: layout metadata does not select the operation."""

from .bitops import compile_bit_reverse
from .classifications import compile_mod_classification
from .collectives import compile_gather, compile_square_sum
from .colors import compile_hsv_to_rgb
from .compiler import CompileError
from .float_maps import compile_float_map
from .generators import compile_literal, compile_range
from .inversions import compile_inversions
from .maps import compile_map
from .matrices import compile_matrix_square
from .membership import compile_membership
from .predicates import compile_threshold
from .text import compile_fizzbuzz_text
from .transposes import compile_transpose


def compile_program(
    source,
    *,
    inputs,
    output,
    atol=None,
    row_partition="local",
    opt="opt",
    assembler=None,
):
    """Select an applicable semantic lowering from source/types/layout.

    All accepted candidates must recognize the complete source operation and
    check their domain contract. Unsupported programs fail closed. This is a
    restricted Python frontend, not execution of arbitrary Python code.
    """
    common = {"inputs": inputs, "output": output, "opt": opt, "assembler": assembler}
    candidates = [
        (compile_map, {}),
        (compile_threshold, {}),
        (compile_mod_classification, {}),
        (compile_membership, {}),
        (compile_range, {}),
        (compile_literal, {}),
        (compile_fizzbuzz_text, {}),
        (compile_transpose, {"row_partition": row_partition}),
        (compile_gather, {"row_partition": row_partition}),
        (compile_bit_reverse, {"row_partition": row_partition}),
        (compile_inversions, {"row_partition": row_partition}),
    ]
    if atol is not None:
        candidates += [
            (compile_float_map, {"atol": atol}),
            (compile_square_sum, {"atol": atol, "row_partition": row_partition}),
            (compile_matrix_square, {"atol": atol, "row_partition": row_partition}),
            (compile_hsv_to_rgb, {"atol": atol, "row_partition": row_partition}),
        ]
    successful, rejected = [], []
    for lower, options in candidates:
        try:
            compiled = lower(source, **common, **options)
        except CompileError as exc:
            rejected.append({"lowering": lower.__name__, "reason": str(exc)})
        else:
            successful.append((compiled, lower.__name__))
    if not successful:
        raise CompileError(
            "No supported lowering matches source/domain/layout. "
            + "; ".join(f"{row['lowering']}: {row['reason']}" for row in rejected)
        )
    chosen, lowering = min(successful, key=lambda item: item[0].report["lines"])
    chosen.report["frontend"] = "restricted Python, source-driven semantic matching"
    chosen.report["chosen_lowering"] = lowering
    chosen.report["applicable_lowerings"] = [
        {"lowering": name, "lines": compiled.report["lines"]}
        for compiled, name in successful
    ]
    return chosen
