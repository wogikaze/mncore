#!/bin/bash
# For each DRAM-writing MV basic mode at n=32704, write zeros over a unique-initialised
# DRAM and locate the last written long word by dumping the boundary indices.
set -u
R="python3 runner.py"
echo "### baseline: DRAM unique init at D0,D32703,D32704"
printf 'mvnop\n' > progs/b_base.vsm
$R progs/b_base.vsm --init unique --dump 0 --dump 32703 --dump 32704

echo
echo "### mvp/n32704 PDM->DRAM single  (expect 32704 longs in group0)"
cat > progs/b_mvp_pdm.vsm <<'V'
mvp/n32704 $lc0@.0 $p0
mvp/n32704 $p0@0 $d0@0
V
$R progs/b_mvp_pdm.vsm --init unique --dump 0 --dump 32703 --dump 32704

echo
echo "### mvp/n32704 L2BM->DRAM parallel (expect 32704 longs per group)"
printf 'mvp/n32704 $lc0@.0 $d0\n' > progs/b_mvp_l2bm_par.vsm
$R progs/b_mvp_l2bm_par.vsm --init unique --dump 0 --dump 32703 --dump 32704

echo
echo "### mvp/n32704 L2BM->DRAM single (group0)"
printf 'mvp/n32704 $lc0@0.0 $d0@0\n' > progs/b_mvp_l2bm_single.vsm
$R progs/b_mvp_l2bm_single.vsm --init unique --dump 0 --dump 32703 --dump 32704

echo
echo "### mvd/n32704 PDM->DRAM distribute (expect 32704/4=8176 longs per DRAM)"
cat > progs/b_mvd.vsm <<'V'
mvp/n32704 $lc0@.0 $p0
mvd/n32704 $p0@0 $d0
V
$R progs/b_mvd.vsm --init unique --dump 0 --dump 8175 --dump 8176

echo
echo "### mvr2dfadd/n32704 L2BM->DRAM (expect 32704 longs per DRAM)"
printf 'mvr2dfadd/n32704 $lc0 $d0\n' > progs/b_mvr2.vsm
$R progs/b_mvr2.vsm --init unique --dump 0 --dump 32703 --dump 32704

echo
echo "### mvr4dfadd/n32704 L2BM->DRAM (expect 32704/2=16352 longs per DRAM)"
printf 'mvr4dfadd/n32704 $lc0 $d0\n' > progs/b_mvr4.vsm
$R progs/b_mvr4.vsm --init unique --dump 0 --dump 16351 --dump 16352

echo
echo "### mvrdfadd/n32704 L2BM->DRAM (expect 32704/4=8176 longs per DRAM)"
printf 'mvrdfadd/n32704 $lc0 $d0\n' > progs/b_mvr.vsm
$R progs/b_mvr.vsm --init unique --dump 0 --dump 8175 --dump 8176
