"""Issue resource counts for a fixed instruction sequence.

The lower bound holds for the current instructions and unit assignment. It ignores
latencies, memory ports and dependencies, and is not a bound for other algorithms.
"""

from collections import Counter

from .machine import parse_program, words

ISSUE_UNITS = ("alu", "mau", "mwrite", "mread", "l1bm", "l1bm-turnaround",
               "l2bm", "l2bmdarw", "mv")


def program_stats(source: str) -> dict:
    steps = parse_program(source)
    lines = words(steps)
    counts = Counter(i.unit for step in steps for i in step.instrs if i.unit in ISSUE_UNITS)
    lower = max(counts.values(), default=0)
    return {
        "lines": lines,
        "instructions": sum(counts.values()),
        "nop_lines": sum(step.nop for step in steps),
        "resource_lower_bound": lower,
        "scheduling_gap": lines - lower,
        "bottleneck_units": [u for u in ISSUE_UNITS if counts[u] == lower and lower],
        "unit_counts": {u: counts[u] for u in ISSUE_UNITS},
        "unit_utilization": {u: counts[u] / lines if lines else 0.0 for u in ISSUE_UNITS},
    }
