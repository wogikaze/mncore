import unittest

from mncompile.stats import program_stats


class IssueStatistics(unittest.TestCase):
    def test_parallel_issue_turnaround_and_nop_expansion(self):
        stats = program_stats("""# parallel issue and expanded nops
lpassa $lm0v $lr0v; fvmul $ls0v $ln0v $nowrite; l1bmd $lm0v $lbi
l1bmd $lbi $ln8v
nop/3
noforward
""")
        self.assertEqual(stats["lines"], 6)
        self.assertEqual(stats["instructions"], 4)
        self.assertEqual(stats["nop_lines"], 3)
        self.assertEqual(stats["resource_lower_bound"], 1)
        self.assertEqual(stats["scheduling_gap"], 5)
        self.assertEqual(stats["unit_counts"]["l1bm"], 1)
        self.assertEqual(stats["unit_counts"]["l1bm-turnaround"], 1)
        self.assertEqual(stats["unit_utilization"]["mau"], 1 / 6)

    def test_serial_alu_is_at_its_resource_bound(self):
        stats = program_stats("lpassa $lm0v $ln0v\niadd $lr0v $ls0v $ln8v\n")
        self.assertEqual(stats["resource_lower_bound"], 2)
        self.assertEqual(stats["scheduling_gap"], 0)
        self.assertEqual(stats["bottleneck_units"], ["alu"])

    def test_empty_program(self):
        stats = program_stats("")
        self.assertEqual(stats["lines"], 0)
        self.assertEqual(stats["resource_lower_bound"], 0)
        self.assertFalse(any(stats["unit_utilization"].values()))
