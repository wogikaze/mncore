"""Record assemble3 boundary observations for selected instruction fields."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import resource
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
ASSEMBLER = REPO / "judge/judge-py/mncore2_emuenv/assemble3"
MANUAL_MV_SOURCES = sorted((REPO / "docs/mncore_llm/chapters/ch03").glob("section-3.5.8.*.md"))
CASES = {
    "nop_zero": ("nop/0\n", True, 0),
    "nop_one": ("nop/1\n", True, 1),
    "nop_with_wait": ("nop; wait i01\n", True, 1),
    "nop_with_alu": ("nop; iadd $lm0 $ln0\n", False, None),
    "nop_zero_with_wait": ("nop/0; wait i01\n", False, None),
    "wait_zero_tag": ("nop; wait i00\n", False, None),
    "wait_tag_1": ("nop; wait i01\n", True, 1),
    "wait_tag_255": ("nop; wait iFF\n", True, 1),
    "wait_tag_256": ("nop; wait i100\n", False, None),
    "omr_0": ("zero $omr0\n", False, None),
    "omr_1": ("zero $omr1\n", True, 1),
    "omr_15": ("zero $omr15\n", True, 1),
    "omr_16": ("zero $omr16\n", False, None),
    "lpassa_multi_output_three_banks": (
        "lpassa $lm0 $ln0 $lr0 $ls0\n", True, 1),
    "lpassa_duplicate_output_bank": (
        "lpassa $lm0 $ln0 $ln2\n", False, None),
    "zero_multi_output_four_memories_and_omr": (
        "zero $lm0 $ln0 $lr0 $ls0 $omr1\n", True, 1),
    "zero_multi_output_all_six_categories": (
        "zero $lm0 $ln0 $lr0 $ls0 $t $omr1\n", True, 1),
    "zero_single_nowrite_output": ("zero $nowrite\n", True, 1),
    "zero_duplicate_nowrite_outputs": ("zero $nowrite $nowrite\n", False, None),
    "zero_duplicate_lm0_distinct_addresses": (
        "zero $lm0 $lm4\n", False, None),
    "zero_duplicate_omr_distinct_entries": (
        "zero $omr1 $omr2\n", False, None),
    "matrix_write_two_matrix_destinations": (
        "gmwrite $aluf $lx0 $ly0\n", False, None),
    "zero_duplicate_lm0_output": ("zero $lm0 $lm2\n", False, None),
    "zero_duplicate_lm1_output": ("zero $ln0 $ln2\n", False, None),
    "zero_duplicate_grf0_output": ("zero $lr0 $lr2\n", False, None),
    "zero_duplicate_grf1_output": ("zero $ls0 $ls2\n", False, None),
    "zero_duplicate_t_output": ("zero $t $t\n", False, None),
    "zero_duplicate_mask_output": (
        "zero $omr1 $omr2\n", False, None),
    "zero_nowrite_with_other_output": (
        "zero $nowrite $omr1\n", False, None),
    "matrix_row_15": ("gmread $lx15 $nowrite\n", True, 1),
    "matrix_row_16": ("gmread $lx16 $nowrite\n", False, None),
    "hbfn_6": ("hbfn/6 $lm0 $ln0\n", True, 1),
    "hbfn_9": ("hbfn/9 $lm0 $ln0\n", True, 1),
    "hbfn_10": ("hbfn/10 $lm0 $ln0\n", False, None),
    "hbfe_6": ("hbfe/6 $lm0 $ln0\n", True, 1),
    "hbfe_9": ("hbfe/9 $lm0 $ln0\n", True, 1),
    "hbfe_10": ("hbfe/10 $lm0 $ln0\n", False, None),
    "hbfe_5": ("hbfe/5 $lm0 $ln0\n", False, None),
    "hbfe_11": ("hbfe/11 $lm0 $ln0\n", False, None),
    "hbfn_5": ("hbfn/5 $lm0 $ln0\n", False, None),
    "hbfn_11": ("hbfn/11 $lm0 $ln0\n", False, None),
    "imr_selector_0": ("lpassa $lm0 $ln0/$imr0\n", True, 1),
    "imr_selector_1": ("lpassa $lm0 $ln0/$imr1\n", True, 1),
    "imr_selector_31": ("lpassa $lm0 $ln0/$imr31\n", True, 1),
    "imr_selector_32": ("lpassa $lm0 $ln0/$imr32\n", False, None),
    "imr_selector_255": ("lpassa $lm0 $ln0/$imr255\n", False, None),
    "mask_directive_n_0": ("maskn 0\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_n_1": ("maskn 1\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_n_31": ("maskn 31\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_n_32": ("maskn 32\nlpassa $lm0 $ln0\n", False, None),
    "mask_directive_l_31": ("maskln 31\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_l_32": ("maskln 32\nlpassa $lm0 $ln0\n", False, None),
    "mask_directive_ll_31": ("masklln 31\nlpassa $lm0 $ln0\n", True, 1),
    "mask_directive_ll_32": ("masklln 32\nlpassa $lm0 $ln0\n", False, None),
    "raw_operand_alu_source": ("iadd $qraw $lm0 $ln0\n", False, None),
    "raw_operand_alu_destination": ("iadd $lm0 $ln0 $qraw\n", False, None),
    "raw_operand_zero_destination": ("zero $qraw\n", False, None),
    "raw_operand_matrix_source": ("gmread $qraw $nowrite\n", False, None),
    "raw_operand_l1bm_source": ("l1bmm $qraw $lb0\n", False, None),
    "mask_application_same_width": (
        "lpassa $lm0v $lr0v/$imr1; l1bmm $lb0 $ls0v/$imr1\n", True, 1),
    "mask_application_conflicting_width": (
        "lpassa $lm0v $lr0v/$imr1; l1bmm $lb0 $ls0v/$llimr1\n", False, None),
    "mask_application_conflicting_entry": (
        "lpassa $lm0v $lr0v/$imr1; l1bmm $lb0 $ls0v/$imr2\n", False, None),
    "mask_flush_conflicting_entry": (
        "lpassa/$imr1 $lm0v $lr0v/$imr2\n", False, None),
    "omr_cross_group_same_entry": (
        "gmfma $ly $ls0v $lr0v $ln0v $omr1; lpassa $lt $omr1\n", False, None),
    "omr_cross_group_different_entries": (
        "gmfma $ly $ls0v $lr0v $ln0v $omr1; lpassa $lt $omr2\n", False, None),
    "mask_flag_read_with_omr_write_same_entry": (
        "lpassa $lm0v $lr0v/$imr1; gmfma $ly $ls0v $lr0v $ln0v $omr1\n", True, 1),
    "mask_flag_read_with_omr_write_different_entry": (
        "lpassa $lm0v $lr0v/$imr1; gmfma $ly $ls0v $lr0v $ln0v $omr2\n", True, 1),
    "l1bm_forward_source": ("l1bmm $lb0 $lr0v\n", True, 1),
    "l1bm_turnaround_forward_source": (
        "l1bmm@2 $lr0v $lb0\nl1bmm $lbi $lm0v\n", True, 2),
    "l1bm_duplicate_lbf_write": (
        "l1bmm@2 $lr0v $lb0\nl1bmm $lb16 $lr8v; l1bmm $lbi $lm0v\n", False, None),
    "l2bmdars_parallel_l2bm_exception": (
        "l2bmdars $lc0@.0 $dar0; l2bmb $lc256 $lb0\n", False, None),
    "debug_set_record": ("d set $lm0n0c0b0m0p0 1 0000000000000000\n", True, 1),
    "debug_get_record": ("d get $lm0n0c0b0m0p0 1\n", True, 1),
    "dram_set_record": ("r 0 000000000 000001 0000000000000000\n", True, 1),
    "l1bm_long_addr_0": ("l1bmm $lb0 $nowrite\n", True, 1),
    "l1bm_long_addr_8188": ("l1bmm $lb8188 $nowrite\n", True, 1),
    "l1bm_long_addr_8192": ("l1bmm $lb8192 $nowrite\n", False, None),
    "l1bm_mab_16": ("l1bmm@16 $lm0 $lb0\n", False, None),
    "l1bm_m4_mab_16": ("l1bmm4@16 $lr0v $lb0\n", False, None),
    "l1b_set_address_8": ("l2bmb@8/0 $lc0 $lb0\n", False, None),
    "l1b_set_immode_8": ("l2bmb@0/8 $lc0 $lb0\n", False, None),
    "l2bm_dar_l2b_0": ("l2bmdars $lc1024@.0 $dar0; l2bmdarw\n", True, 1),
    "l2bm_dar_l2b_1": ("l2bmdars $lc1024@.1 $dar0; l2bmdarw\n", True, 1),
    "l2bm_dar_l2b_2": ("l2bmdars $lc1024@.2 $dar0; l2bmdarw\n", False, None),
    "l2bmdars_with_l2bmb": (
        "l2bmdars $lc0@.0 $dar0; l2bmb $lc0 $lb0\n", False, None),
    "l2bmdars_with_l2bmb2": (
        "l2bmdars $lc0@.0 $dar0; l2bmb2 $lc0 $lb0\n", False, None),
    "l2bmdars_with_l2bmd": (
        "l2bmdars $lc0@.0 $dar0; l2bmd $lc0 $lb0\n", False, None),
    "l2bmdars_with_l2bm_from_l1b": (
        "l2bmdars $lc0@.0 $dar0; l2bm@1 $lb0 $lc0\n", False, None),
    "l2bmdars_with_l2bm_reduce": (
        "l2bmdars $lc0@.0 $dar0; l2bmrdfadd $lb0 $lc0\n", False, None),
    "l2bmdars_with_l2bm_reduce2": (
        "l2bmdars $lc0@.0 $dar0; l2bmr2dfadd $lb0 $lc0\n", False, None),
    "l2bmdars_with_l2bm_internal_multicast": (
        "l2bmdars $lc0@.0 $dar0; l2bmi@0/4 $lb0 $lb0\n", False, None),
    "dar_addr_1023": ("l2bmdars $lc1024@.0 $dar1023; l2bmdarw\n", True, 1),
    "dar_addr_1024": ("l2bmdars $lc1024@.0 $dar1024; l2bmdarw\n", False, None),
    "mabdiff_minus256": ("l1bmd-256 $lm0 $lb0\n", False, None),
    "mabdiff_plus256": ("l1bmd+256 $lm0 $lb0\n", False, None),
    "region_address_cycle0_max": ("lpassa $m[4095,0,0,0] $n0\n", True, 1),
    "region_address_cycle1_max": ("lpassa $m[0,4095,0,0] $n0\n", True, 1),
    "region_address_cycle2_max": ("lpassa $m[0,0,4095,0] $n0\n", True, 1),
    "region_address_cycle3_max": ("lpassa $m[0,0,0,4095] $n0\n", True, 1),
    "region_address_cycle3_overflow": ("lpassa $m[0,0,0,4096] $n0\n", False, None),
    "madpe_2": ("lpassa $m0j2 $n0\n", True, 1),
    "madpe_3": ("lpassa $m0j3 $n0\n", True, 1),
    "madpe_4": ("lpassa $m0j4 $n0\n", False, None),
    "mv_size_0": ("mvp/n0 $d0 $lc0@.0\n", True, 1),
    "mv_size_1": ("mvp/n1 $d0 $lc0@.0\n", False, None),
    "mv_size_64": ("mvp/n64 $d0 $lc0@.0\n", True, 1),
    "mv_size_32704": ("mvp/n32704 $d0 $lc0@.0\n", True, 1),
    "mv_size_32768": ("mvp/n32768 $d0 $lc0@.0\n", False, None),
    "mv_size_65536": ("mvp/n65536 $d0 $lc0@.0\n", False, None),
    "mv_then_pe_same_line": (
        "mvp/n64 $d0 $lc0@.0; iadd $lm0 $ln0\n", False, None),
    "pe_then_mv_same_line": (
        "iadd $lm0 $ln0; mvp/n64 $d0 $lc0@.0\n", False, None),
    "l1bm_width2_max": ("l1bmm $lb8188 $nowrite\n", True, 1),
    "l1bm_width2_unaligned": ("l1bmm $lb8190 $nowrite\n", False, None),
    "l1bm_width2_capacity": ("l1bmm $lb8192 $nowrite\n", False, None),
    "l1bm_width4_max": ("l1bmm $llb8184 $nowrite\n", True, 1),
    "l1bm_width4_unaligned": ("l1bmm $llb8188 $nowrite\n", False, None),
    "l1bm_width4_capacity": ("l1bmm $llb8192 $nowrite\n", False, None),
    "l2bm_address_32736": ("l2bmb $lc32736 $lb0\n", True, 1),
    "l2bm_address_32752": ("l2bmb $lc32752 $lb0\n", True, 1),
    "l2bm_address_32760": ("l2bmb $lc32760 $lb0\n", False, None),
    "l2bm_address_32768": ("l2bmb $lc32768 $lb0\n", False, None),
    "matrix_read_width2": ("gmread $lx0 $nowrite\n", True, 1),
    "matrix_read_width4": ("gmread $llx0 $nowrite\n", False, None),
    "matrix_write_width2": ("gmwrite $aluf $lx0\n", True, 1),
    "matrix_write_width4": ("gmwrite $aluf $llx0\n", False, None),
    "matrix_mul_width2": ("gmmul $lx $aluf $ln0v4\n", True, 1),
    "matrix_mul_width4": ("gmmul $llx $aluf $ln0v4\n", True, 1),
}


def manual_mv_cases() -> dict[str, tuple[str, bool, int | None]]:
    """Build size-boundary probes from each documented MV grammar production."""
    values = {
        "op": "dfadd", "size": "64", "tag": "i01",
        "addr_p": "0", "addr_d": "0", "addr_c": "0", "addr0": "0", "addr1": "0",
        "group_p": "0", "group_d": "0", "group_c": "0", "group0": "0", "group1": "0",
        "group": "0", "l2b_c": "0",
    }
    cases = {}
    for path in MANUAL_MV_SOURCES:
        match = re.search(r"```(?:txt)?文法\s*\n(.*?)```", path.read_text(), re.S)
        if not match:
            continue
        productions = [line.strip() for line in match.group(1).splitlines() if line.strip()]
        production = next((line for line in productions if line.startswith("mv")), None)
        if production is None:
            continue
        section = re.search(r"3\.5\.8\.(\d+)", path.name).group(1)
        if production == "mvnop":
            cases[f"manual_mv_{section}_mvnop"] = ("mvnop\n", True, 1)
            continue
        template = production.replace("[<tag>]", "")
        for key, value in values.items():
            template = template.replace(f"<{key}>", value)
        if re.search(r"<[a-zA-Z0-9_]+>", template):
            raise ValueError(f"unfilled MV grammar field in {path}: {template}")
        for size, accepted in ((64, True), (32704, True), (32768, False)):
            source = template.replace("/n64", f"/n{size}") + "\n"
            cases[f"manual_mv_{section}_size_{size}"] = (source, accepted, 1 if accepted else None)
    return cases


CASES.update(manual_mv_cases())
L2BMDARS_COMPANIONS = {
    "bcast": "l2bmb $lc256 $lb0",
    "bcast2": "l2bmb2 $lc256 $lb0",
    "distrib": "l2bmd $lc256 $lb0",
    "froml1b": "l2bm@0 $lb0 $lc256",
    "reduce": "l2bmrdfadd $lb0 $lc256",
    "reduce2": "l2bmr2dfadd $lb0 $lc256",
    "gather": "l2bmd $lb0 $lc256",
    "imcast": "l2bmi@0/4 $lb0 $lb0",
}
for selector in range(2):
    for opcode, expression in L2BMDARS_COMPANIONS.items():
        CASES[f"l2bmdars_{opcode}_selector{selector}"] = (
            f"l2bmdars $lc0@.{selector} $dar0; {expression}\n", False, None)
for index in range(2, 31):
    CASES[f"imr_selector_{index}"] = (f"lpassa $lm0 $ln0/$imr{index}\n", True, 1)
    CASES[f"mask_directive_n_{index}"] = (f"maskn {index}\nlpassa $lm0 $ln0\n", True, 1)
for index in range(33, 255):
    CASES[f"imr_selector_{index}"] = (f"lpassa $lm0 $ln0/$imr{index}\n", False, None)
for index in range(33, 256):
    CASES[f"mask_directive_n_{index}"] = (
        f"maskn {index}\nlpassa $lm0 $ln0\n", False, None)
for index in [*range(31), *range(33, 256)]:
    accepted = index < 32
    CASES[f"mask_directive_l_{index}"] = (
        f"maskln {index}\nlpassa $lm0 $ln0\n", accepted, 1 if accepted else None)
    CASES[f"mask_directive_ll_{index}"] = (
        f"masklln {index}\nlpassa $lm0 $ln0\n", accepted, 1 if accepted else None)
for index in range(2, 15):
    CASES[f"omr_{index}"] = (f"zero $omr{index}\n", True, 1)
for index in range(16, 256):
    CASES[f"omr_{index}"] = (f"zero $omr{index}\n", False, None)
for index in range(16):
    CASES[f"matrix_row_{index}"] = (f"gmread $lx{index} $nowrite\n", True, 1)
for index in range(6, 10):
    CASES[f"hbfn_{index}"] = (f"hbfn/{index} $lm0 $ln0\n", True, 1)
    if index not in {6, 9}:
        CASES[f"hbfe_{index}"] = (f"hbfe/{index} $lm0 $ln0\n", True, 1)
for index in range(256):
    accepted = 6 <= index <= 9
    CASES[f"hbfn_{index}"] = (
        f"hbfn/{index} $lm0 $ln0\n", accepted, 1 if accepted else None)
    CASES[f"hbfe_{index}"] = (
        f"hbfe/{index} $lm0 $ln0\n", accepted, 1 if accepted else None)
for tag in range(1, 257):
    CASES[f"wait_tag_{tag}"] = (
        f"nop; wait i{tag:02X}\n", tag < 256, 1 if tag < 256 else None)
for prefix, aligned_max, capacity in [
    ("m", 4095, 4096), ("n", 4095, 4096),
    ("r", 511, 512), ("s", 511, 512),
    ("lm", 4094, 4096), ("ln", 4094, 4096),
    ("lr", 510, 512), ("ls", 510, 512),
    ("llm", 4092, 4096), ("lln", 4092, 4096),
    ("llr", 508, 512), ("lls", 508, 512),
]:
    other_lm = "m0" if prefix in {"n", "ln", "lln"} else "n0"
    CASES[f"memory_{prefix}_aligned_max"] = (
        f"lpassa ${prefix}{aligned_max} ${other_lm}\n", True, 1)
    CASES[f"memory_{prefix}_capacity"] = (
        f"lpassa ${prefix}{capacity} ${other_lm}\n", False, None)
for entry in range(8):
    for immode in range(8):
        CASES[f"l1b_set_{entry}_{immode}"] = (
            f"l2bmb@{entry}/{immode} $lc0 $lb0\n", True, 1)
for entry in range(9):
    CASES[f"l2bm_from_l1b_{entry}"] = (
        f"l2bm@{entry} $lb0 $lc0\n", entry < 8, 1 if entry < 8 else None)
for entry in range(16):
    CASES[f"l1bm_mab_{entry}"] = (
        f"l1bmm@{entry} $lm0 $lb0\n", True, 1)
    CASES[f"l1bm_m4_mab_{entry}"] = (
        f"l1bmm4@{entry} $lr0v $lb0\n", True, 1)
for offset in range(-255, 256):
    opcode = f"l1bmd{offset:+d}" if offset else "l1bmd+0"
    CASES[f"mabdiff_{offset:+d}"] = (f"{opcode} $lm0 $lb0\n", True, 1)
    CASES[f"mabdiff_distrib_{offset:+d}"] = (
        f"{opcode} $lb0 $lr0v\n", True, 1)
CASES["mabdiff_distrib_minus256"] = ("l1bmd-256 $lb0 $lr0v\n", False, None)
CASES["mabdiff_distrib_plus256"] = ("l1bmd+256 $lb0 $lr0v\n", False, None)
for width, expected in [("mb", True), ("lmb", True), ("llmb", False)]:
    CASES[f"bar_width_{width}"] = (
        f"lpassa $n0 ${width}\n", expected, 1 if expected else None)
CASES.update({
    "bar_write_lm0": ("iadd $lr0 $lr0 $mb\n", True, 1),
    "bar_write_lm1": ("iadd $ls0 $ls0 $nb\n", True, 1),
    "bar_write_and_read_other_bank": (
        "iadd $lr0 $lr0 $mb; gmmul $lx $ln0v $ls0v\n", True, 1),
    "bar_write_and_read_same_bank": (
        "iadd $lr0 $lr0 $mb; gmmul $lx $m0 $lr0v\n", False, None),
    "bar_write_and_data_write_same_bank": (
        "iadd $lr0 $lr0 $mb $m0\n", False, None),
})


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
            output_lines = result.stdout.splitlines() if accepted else []
            words = len(output_lines) if accepted else None
            encoded_words = []
            auxiliary_output_kinds = []
            output_shape_valid = True
            for line in output_lines:
                fields = line.split()
                kind = fields[0] if fields else ""
                if kind in {"j", "m"}:
                    word = {
                        "kind": kind,
                        "bit_width": len(fields[1]) if len(fields) == 2 else None,
                        "binary": len(fields) == 2 and set(fields[1]) <= {"0", "1"},
                    }
                    encoded_words.append(word)
                    output_shape_valid = output_shape_valid and word["binary"] and word["bit_width"] == {"j": 426, "m": 82}[kind]
                elif kind in {"d", "r"}:
                    auxiliary_output_kinds.append(kind)
                else:
                    output_shape_valid = False
            observation = {
                "case": name,
                "source": source.rstrip("\n"),
                "accepted": accepted,
                "assembler_output_lines": words,
                "encoded_words": encoded_words,
                "auxiliary_output_kinds": auxiliary_output_kinds,
                "diagnostic": (result.stderr.splitlines() or [""])[0],
                "matches_expected": accepted == expected_accept and words == expected_words
                    and (not accepted or output_shape_valid),
            }
            if result.returncode < 0:
                observation["returncode"] = result.returncode
            observations.append(observation)
    sources = [ASSEMBLER, REPO / "viz/core/src/vsm.rs", REPO / "viz/core/src/mv.rs",
               REPO / "viz/core/src/blockop.rs", REPO / "judge/judge-py/judge.py",
               Path(__file__).resolve(), *MANUAL_MV_SOURCES]
    report = {
        "schema_version": 1,
        "experiment": "selected assembler parsing and encoding boundaries",
        "scope": "Only listed probes. Acceptance/encoding evidence is not proof of complete ISA ranges or semantics.",
        "tool_hashes": [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p)} for p in sources],
        "observations": observations,
        "findings": [
            "Every observed accepted `j` instruction output is a binary 426-bit word and every `m` instruction output is a binary 82-bit word. Accepted debug/DRAM records use `d`/`r` formats and are tracked separately because the default judge strips them from the scored instruction stream. These probes do not prove the output format for every accepted source line.",
            "nop/0 is accepted and emits zero instruction words; nop/0 with a wait is rejected, so the zero-count no-wait form can be erased during normalization.",
            "wait i00 is rejected; i01 and iFF are accepted; i100 is rejected.",
            "Every u8 OMR destination selector was probed: exactly $omr1..$omr15 are accepted; $omr0 and $omr16..$omr255 are rejected.",
            "Every u8 mask-read selector was probed: $imr0..$imr31 are accepted and $imr32..$imr255 are rejected. Every u8 selector was also probed for maskn, maskln, and masklln directives; each accepts 0..31 and rejects 32..255. This conflicts with the Rust MaskSource comment claiming entries 1 through 15.",
            "Representative unknown `$qraw` operands in ALU source/destination, zero destination, matrix-read source, and L1BM source positions produce no assembler output; assemble3 aborts with return code -6 on these malformed tokens. This is sampled rejection evidence, not a proof over every Raw string.",
            "SDM 3.6.4 requires simultaneous mask applications to use the same width; Section 3.6.2.1 also requires matching variable entry addresses. The same-width pair is accepted, while mixed widths, mixed entries, and a write-mask/zero-flush entry mismatch are rejected.",
            "Mask-flag reads and OMR writes use distinct issue ports: a masked lpassa can issue with gmfma writing either the same or a different OMR entry. Multiple variable mask reads still require one shared entry, as shown by the accepted and rejected mask-application pair probes.",
            "SDM 3.6.4 treats mask registers as PE operands and disallows multiple writes to that operand in one step. Two otherwise accepted operations that write OMR are rejected together, both for the same entry and for different entries.",
            "After seeding the turnaround buffer with a valid PE-to-L1BM transfer, an ordinary L1BM source and the turnaround source $lbi are each accepted alone. Issuing both to PE destinations together is rejected with an l1bm_emit conflict, an implicit $lbf write conflict across the distinct L1BM issue groups.",
            "The June 2026 manual's Section 3.6.4 describes an l2bmdars exception for simultaneous issue with another L2BM operation, but the bundled assemble3 rejects the focused l2bmdars+l2bmb line. The local encoder/model agreement is unresolved against the newer manual.",
            "The l2bmdars companion matrix also rejected eight L2BM operation classes at each selector .0 and .1. This broadens the bundled assembler evidence but does not identify the newer manual's special exception or prove it cannot occur.",
            "Matrix rows 0 through 15 are accepted; row 16 is rejected.",
            "PE destination lists are not sized by source arity: lpassa accepts three outputs across LM1/GRF0/GRF1, and zero accepts LM0/LM1/GRF0/GRF1 plus OMR. The sampled duplicate-bank and nowrite combinations are rejected; this is not an exhaustive output grammar proof.",
            "The issue checker now mirrors the sampled assembler rule that destination banks cannot repeat within one expression and `$nowrite` must be the sole destination.",
            "Every u8 argument was probed for hbfe and hbfn; both accept exactly /6 through /9.",
            "LM0/LM1 and GRF0/GRF1 accept aligned final addresses at widths 1, 2, and 4; their single-word capacities are respectively 4096 and 512, and the capacity address is rejected.",
            "Each of the four explicit LM0 cycle addresses accepts 4095 and rejects 4096; madpe values 0 through 3 are accepted and 4 is rejected.",
            "All 64 L1B set address/immode pairs in 0..7 are accepted, and address 8 and immode 8 are rejected; `l2bm@<l1b>` accepts 0..7 and rejects 8. Base-address register writes accept widths 1 and 2 but reject width 4.",
            "For every documented MV grammar in Sections 3.5.8.2–3.5.8.25, generated zero-address probes accept sizes 64 and 32704 and reject 32768. The simple operand combinations are sampled evidence, not a proof of all accepted operands. The separate mvp probes show size zero is accepted, size one is rejected, and the size-field overflow at 32768 is rejected.",
            "L1BM width-2 addresses require 4-word alignment and width-4 addresses require 8-word alignment, within the 8192-long-word capacity. The L2BM transfer source accepts 16-aligned addresses through 32752 and rejects 32760 (alignment) and 32768 (range).",
            "Wait tags 1 through 255 are accepted; 0 and 256 are rejected.",
            "Matrix rows 0..15 were checked using gmread. The tested matrix operand widths are instruction-specific: gmread/gmwrite accept width 2 and reject width 4, while gmmul accepts widths 2 and 4.",
            "$lb8188 is accepted while $lb8192 fails the 13-bit encoding field; the L1BM address must also be 4-word aligned. Every l1bmm@ and l1bmm4@ selector 0..15 is accepted, and @16 is rejected for both forms.",
            "DAR address 1023 is accepted and 1024 is rejected; `$lc...@.<l2b>` accepts selectors 0 and 1 and rejects 2.",
            "For l1bmd, each explicit signed offset from -255 through +255 was accepted in both operand directions (PE-to-L1BM gather and L1BM-to-PE distribution); -256 and +256 were rejected in both directions. The manual documents useful offsets 0..15. The Rust visualizer parser now stores the value in i16 and enforces this experimentally established assembler range; its boundary regression is separate from this assembler-only probe. Neither check proves global parser completeness.",
            "The assembler accepts d set, d get and r input records, but the challenge judge's default solution sanitizer retains only j/m instruction rows; these records are filtered before execution. The scored program therefore excludes debug and DRAM initialization records.",
            "A zero instruction with one destination in each of LM0, LM1, GRF0, GRF1, T and OMR is accepted; duplicate destinations within each of those six categories are rejected. This bounds observed destination categories for these probes, but Rust's VSM parser itself still stores all tokens after the fixed source prefix as destinations, and the assembler probes are not a universal parser-to-encoding theorem.",
            "Same-expression destination checks reject duplicate output classes even when the operand values differ (LM0 at two addresses, two OMR entries), reject repeated nowrite, and reject multiple matrix-write destinations. A single nowrite destination is accepted. These checks support finite destination arity for the sampled opcodes but do not establish a bound for every opcode spelling.",
            "Judge flags can preserve d get/d set, but the normal challenge invocation does not set them; the d-set invalidation applies only when such a record is retained.",
            "Selected valid-operand combinations of l2bmdars with l2bmb, l2bmb2, l2bmd, l2bm@, l2bmr*, l2bmr2* and l2bmi were rejected. This does not cover the manual's unspecified special l2bmdars issue condition.",
            "The assembler accepts `nop; wait i01` and rejects nop with an ALU expression; the zero-count nop/wait pair is also rejected. MV and PE expressions cannot be combined on one source line in either order in the tested forms.",
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
