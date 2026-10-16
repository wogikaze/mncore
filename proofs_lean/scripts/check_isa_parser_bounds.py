"""Record assemble3 boundary observations for selected instruction fields."""
from __future__ import annotations

import argparse
import hashlib
import json
import resource
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
ASSEMBLER = REPO / "judge/judge-py/mncore2_emuenv/assemble3"
CASES = {
    "nop_zero": ("nop/0\n", True, 0),
    "nop_one": ("nop/1\n", True, 1),
    "nop_zero_with_wait": ("nop/0; wait i01\n", False, None),
    "wait_zero_tag": ("nop; wait i00\n", False, None),
    "wait_tag_1": ("nop; wait i01\n", True, 1),
    "wait_tag_255": ("nop; wait iFF\n", True, 1),
    "wait_tag_256": ("nop; wait i100\n", False, None),
    "omr_0": ("zero $omr0\n", False, None),
    "omr_1": ("zero $omr1\n", True, 1),
    "omr_15": ("zero $omr15\n", True, 1),
    "omr_16": ("zero $omr16\n", False, None),
    "matrix_row_15": ("gmread $lx15 $nowrite\n", True, 1),
    "matrix_row_16": ("gmread $lx16 $nowrite\n", False, None),
    "hbfn_6": ("hbfn/6 $lm0 $ln0\n", True, 1),
    "hbfn_9": ("hbfn/9 $lm0 $ln0\n", True, 1),
    "hbfn_10": ("hbfn/10 $lm0 $ln0\n", False, None),
    "imr_selector_0": ("lpassa $lm0 $ln0/$imr0\n", True, 1),
    "imr_selector_31": ("lpassa $lm0 $ln0/$imr31\n", True, 1),
    "imr_selector_32": ("lpassa $lm0 $ln0/$imr32\n", False, None),
    "imr_selector_255": ("lpassa $lm0 $ln0/$imr255\n", False, None),
    "mask_directive_n_0": ("maskn 0\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_n_1": ("maskn 1\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_n_31": ("maskn 31\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_n_32": ("maskn 32\nlpassa $lm0 $ln0\n", False, None),
    "debug_set_record": ("d set $lm0n0c0b0m0p0 1 0000000000000000\n", True, 1),
    "debug_get_record": ("d get $lm0n0c0b0m0p0 1\n", True, 1),
    "dram_set_record": ("r 0 000000000 000001 0000000000000000\n", True, 1),
    "l1bm_long_addr_0": ("l1bmm $lb0 $nowrite\n", True, 1),
    "l1bm_long_addr_8188": ("l1bmm $lb8188 $nowrite\n", True, 1),
    "l1bm_long_addr_8192": ("l1bmm $lb8192 $nowrite\n", False, None),
    "l1bm_mab_15": ("l1bmm@15 $lm0 $lb0\n", True, 1),
    "l1bm_mab_16": ("l1bmm@16 $lm0 $lb0\n", False, None),
    "l2bm_dar_l2b_0": ("l2bmdars $lc1024@.0 $dar0; l2bmdarw\n", True, 1),
    "l2bm_dar_l2b_1": ("l2bmdars $lc1024@.1 $dar0; l2bmdarw\n", True, 1),
    "l2bm_dar_l2b_2": ("l2bmdars $lc1024@.2 $dar0; l2bmdarw\n", False, None),
    "dar_addr_1023": ("l2bmdars $lc1024@.0 $dar1023; l2bmdarw\n", True, 1),
    "dar_addr_1024": ("l2bmdars $lc1024@.0 $dar1024; l2bmdarw\n", False, None),
    "mabdiff_minus129": ("l1bmd-129 $lm0 $lb0\n", True, 1),
    "mabdiff_minus128": ("l1bmd-128 $lm0 $lb0\n", True, 1),
    "mabdiff_plus127": ("l1bmd127 $lm0 $lb0\n", True, 1),
    "mabdiff_plus128": ("l1bmd128 $lm0 $lb0\n", True, 1),
}
for index in range(2, 31):
    CASES[f"imr_selector_{index}"] = (f"lpassa $lm0 $ln0/$imr{index}\n", True, 1)
    CASES[f"mask_directive_n_{index}"] = (f"maskn {index}\nlpassa $lm0 $ln0\n", True, 1)
for index in range(2, 15):
    CASES[f"omr_{index}"] = (f"zero $omr{index}\n", True, 1)
for index in range(16):
    CASES[f"matrix_row_{index}"] = (f"gmread $lx{index} $nowrite\n", True, 1)
for index in range(6, 10):
    CASES[f"hbfn_{index}"] = (f"hbfn/{index} $lm0 $ln0\n", True, 1)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    observations = []
    with tempfile.TemporaryDirectory(prefix="mncore-isa-boundaries-") as directory:
        for name, (source, expected_accept, expected_words) in CASES.items():
            vsm = Path(directory) / f"{name}.vsm"
            vsm.write_text(source)
            result = subprocess.run(
                [str(ASSEMBLER), "--instruction-mode", "flat", str(vsm)],
                capture_output=True, text=True, timeout=30,
            )
            accepted = result.returncode == 0
            words = len(result.stdout.splitlines()) if accepted else None
            observations.append({
                "case": name,
                "source": source.rstrip("\n"),
                "accepted": accepted,
                "assembler_output_lines": words,
                "diagnostic": (result.stderr.splitlines() or [""])[0],
                "matches_expected": accepted == expected_accept and words == expected_words,
            })
    sources = [ASSEMBLER, REPO / "viz/core/src/vsm.rs", REPO / "viz/core/src/mv.rs",
               REPO / "viz/core/src/blockop.rs", REPO / "judge/judge-py/judge.py",
               Path(__file__).resolve()]
    report = {
        "schema_version": 1,
        "experiment": "selected assembler parsing and encoding boundaries",
        "scope": "Only listed probes. Acceptance/encoding evidence is not proof of complete ISA ranges or semantics.",
        "tool_hashes": [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p)} for p in sources],
        "observations": observations,
        "findings": [
            "nop/0 is accepted and emits zero instruction words; nop/0 with a wait is rejected, so the zero-count no-wait form can be erased during normalization.",
            "wait i00 is rejected; i01 and iFF are accepted; i100 is rejected.",
            "$omr0 and $omr16 are rejected; $omr1 and $omr15 are accepted.",
            "$imr0, $imr31 are accepted while $imr32 and $imr255 fail encoding. Active mask directives `maskn 0` and `maskn 31` are accepted, while `maskn 32` fails. This conflicts with the Rust MaskSource comment claiming entries 1 through 15.",
            "Matrix rows 0 through 15 are accepted; row 16 is rejected.",
            "hbfn/6 through hbfn/9 are accepted; hbfn/10 is rejected.",
            "$lb8188 is accepted while $lb8192 fails the 13-bit encoding field; the L1BM address must also be 4-word aligned. l1bmm@15 is accepted and @16 is rejected.",
            "DAR address 1023 is accepted and 1024 is rejected; `$lc...@.<l2b>` accepts selectors 0 and 1 and rejects 2.",
            "l1bmd-129, l1bmd-128, l1bmd127, and l1bmd128 are all accepted by assemble3; this is parser/encoding acceptance evidence, not a claim that these offsets are semantically useful.",
            "The assembler accepts d set, d get and r input records, but the challenge judge's default solution sanitizer retains only j/m instruction rows; these records are filtered before execution. The scored program therefore excludes debug and DRAM initialization records.",
            "Judge flags can preserve d get/d set, but the normal challenge invocation does not set them; the d-set invalidation applies only when such a record is retained."
        ],
        "submission_normalization": {
            "source": "judge/judge-py/judge.py",
            "rule": "sanitize_asm retains j/m rows by default; optional flags retain d get/d set; score counts j+m",
            "source_records_accepted_then_removed_from_solution_program": ["d get", "d set", "r"]
        },
        "limitations": [
            "The Rust parser/model and the official assembler are distinct; these probes do not establish parser completeness.",
            "Some rejected probes terminate assemble3 by abort; only nonzero status and its diagnostic are recorded.",
            "No semantic check was performed for accepted out-of-comment-range mask selector values."
        ],
    }
    if not all(row["matches_expected"] for row in observations):
        raise SystemExit("assembler observations differ from expected boundary report")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"recorded {len(observations)} boundary probes in {args.output}")


if __name__ == "__main__":
    main()
