//! Syntax of L1BM and L2BM instruction expressions (SDM 3.6.7, 3.6.8) and reduction opcodes
//! (SDM 3.5.5).

/// Reduction operation of the result reduction network (RRN).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rrn {
    /// Precision: d, f, h (float) or l, i, s (integer).
    pub prec: char,
    pub op: RrnOp,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RrnOp {
    Fadd,
    Max,
    Min,
    Iadd,
    Band,
    And,
    Bor,
    Or,
}

impl Rrn {
    /// Parses a reduction opcode such as `dfadd` or `ibor`, returning it and the rest.
    pub fn parse_prefix(s: &str) -> Option<(Rrn, &str)> {
        let p = s.chars().next()?;
        let rest = &s[1..];
        let ops: &[(&str, RrnOp)] = match p {
            'd' | 'f' | 'h' => &[("fadd", RrnOp::Fadd), ("max", RrnOp::Max), ("min", RrnOp::Min)],
            'l' | 'i' | 's' => &[
                ("iadd", RrnOp::Iadd),
                ("band", RrnOp::Band),
                ("and", RrnOp::And),
                ("bor", RrnOp::Bor),
                ("or", RrnOp::Or),
            ],
            _ => return None,
        };
        for (name, op) in ops {
            if let Some(r) = rest.strip_prefix(name) {
                return Some((Rrn { prec: p, op: *op }, r));
            }
        }
        None
    }

    /// Element width in bits.
    pub fn bits(self) -> u32 {
        match self.prec {
            'd' | 'l' => 64,
            'f' | 'i' => 32,
            _ => 16,
        }
    }
}

/// A set of L1Bs within an L2B (SDM 3.6.7.1), as a bit mask, plus the immode used by l2bmi.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct L1bSet {
    pub mask: u8,
    pub immode: u8,
}

impl L1bSet {
    pub const ALL: L1bSet = L1bSet { mask: 0xff, immode: 7 };

    /// Parses `<l1badr>/<immode>`, `<l1badr>` or `[<list>]`.
    pub fn parse(s: &str) -> Result<L1bSet, String> {
        if let Some(list) = s.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
            let mut mask = 0u8;
            let ids: Vec<u8> = list
                .split(',')
                .map(|x| x.trim().parse::<u8>().map_err(|_| format!("bad L1B list `{s}`")))
                .collect::<Result<_, _>>()?;
            for &b in &ids {
                if b > 7 {
                    return Err(format!("bad L1B number in `{s}`"));
                }
                mask |= 1 << b;
            }
            // The equivalent immode: the bits in which the members differ.
            let base = ids[0];
            let immode = ids.iter().fold(0, |m, &b| m | (b ^ base));
            return Ok(L1bSet { mask, immode });
        }
        let (adr, immode) = match s.split_once('/') {
            Some((a, i)) => (a, i.parse::<u8>().map_err(|_| format!("bad immode in `{s}`"))?),
            None => (s, 0),
        };
        let adr: u8 = adr.parse().map_err(|_| format!("bad L1B number in `{s}`"))?;
        if adr > 7 || immode > 7 {
            return Err(format!("bad L1B set `{s}`"));
        }
        let keep = 7 ^ immode;
        let mask = (0..8u8).filter(|b| b & keep == adr & keep).fold(0, |m, b| m | (1 << b));
        Ok(L1bSet { mask, immode })
    }

    pub fn contains(self, l1b: usize) -> bool {
        (self.mask >> l1b) & 1 == 1
    }
}

/// An L1BM instruction expression (SDM 3.6.8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum L1Op {
    /// `l1bmp`: broadcast to all 64 PEs.
    Pbcast,
    /// `l1bmm`: 16x1 MAB broadcast.
    Mbcast,
    /// `l1bmm@<mab>`: 16x1 individual transfer from one MAB.
    Mwrite { mab: u8 },
    /// `l1bmm4`: 4x4 MAB broadcast.
    M4bcast,
    /// `l1bmm4@<i>`: 4x4 individual transfer from MABs i, 4+i, 8+i, 12+i.
    M4write { mab: u8 },
    /// `l1bmr<rrn>[r]`: 16x1 reduction.
    Reduce { rrn: Rrn, round: bool },
    /// `l1bmr4<rrn>[r]`: 4x4 reduction.
    Reduce4 { rrn: Rrn, round: bool },
    /// `l1bmd[+-n]` from L1BM to PEs: distribution.
    Distrib { mabdiff: i8 },
    /// `l1bmd[+-n]` from PEs to L1BM: gathering.
    Gather { mabdiff: i8 },
}

/// An L2BM instruction expression (SDM 3.6.7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum L2Op {
    /// `l2bmb`: L2BM to L1BM broadcast.
    Bcast { set: L1bSet },
    /// `l2bmb2`: L2BM to L1BM distribution-broadcast.
    Bcast2 { set: L1bSet },
    /// `l2bmd` with $lc source: L2BM to L1BM distribution.
    Distrib { set: L1bSet },
    /// `l2bm@<l1b>`: L1BM to L2BM individual transfer.
    FromL1b { l1b: u8 },
    /// `l2bmr<rrn>`: L1BM to L2BM reduction.
    Reduce { rrn: Rrn, set: L1bSet },
    /// `l2bmr2<rrn>`: L1BM to L2BM gathering reduction.
    Reduce2 { rrn: Rrn },
    /// `l2bmd` with $lb source: L1BM to L2BM gathering.
    Gather,
    /// `l2bmi@<set>`: internal multicast between L1BMs.
    Imcast { set: L1bSet },
    /// `l2bmdars`: L2BM to DAR buffer.
    Dars,
    /// `l2bmdarw`: DAR buffer to DAR.
    Darw,
}

/// Parses the opcode of an L1BM expression. Whether `l1bmd` distributes or gathers depends on
/// the operands, so `to_pe` tells whether the first operand is an L1BM operand.
pub fn parse_l1_opcode(opcode: &str, to_pe: bool) -> Result<L1Op, String> {
    let rest = opcode.strip_prefix("l1bm").ok_or("not an L1BM opcode")?;
    let bad = || format!("unknown L1BM opcode `{opcode}`");
    if rest == "p" {
        return Ok(L1Op::Pbcast);
    }
    if let Some(r) = rest.strip_prefix("m4") {
        return match r.strip_prefix('@') {
            Some(n) => Ok(L1Op::M4write { mab: n.parse().map_err(|_| bad())? }),
            None if r.is_empty() => Ok(L1Op::M4bcast),
            None => Err(bad()),
        };
    }
    if let Some(r) = rest.strip_prefix('m') {
        return match r.strip_prefix('@') {
            Some(n) => Ok(L1Op::Mwrite { mab: n.parse().map_err(|_| bad())? }),
            None if r.is_empty() => Ok(L1Op::Mbcast),
            None => Err(bad()),
        };
    }
    if let Some(r) = rest.strip_prefix('d') {
        let mabdiff: i8 = if r.is_empty() { 0 } else { r.parse().map_err(|_| bad())? };
        return Ok(if to_pe { L1Op::Distrib { mabdiff } } else { L1Op::Gather { mabdiff } });
    }
    if let Some(r) = rest.strip_prefix("r4") {
        let (rrn, tail) = Rrn::parse_prefix(r).ok_or_else(bad)?;
        return Ok(L1Op::Reduce4 { rrn, round: parse_round(tail).ok_or_else(bad)? });
    }
    if let Some(r) = rest.strip_prefix('r') {
        let (rrn, tail) = Rrn::parse_prefix(r).ok_or_else(bad)?;
        return Ok(L1Op::Reduce { rrn, round: parse_round(tail).ok_or_else(bad)? });
    }
    Err(bad())
}

fn parse_round(tail: &str) -> Option<bool> {
    match tail {
        "" => Some(false),
        "r" => Some(true),
        _ => None,
    }
}

/// Parses the opcode of an L2BM expression. `from_l2` tells whether the first operand is L2BM.
pub fn parse_l2_opcode(opcode: &str, from_l2: bool) -> Result<L2Op, String> {
    let rest = opcode.strip_prefix("l2bm").ok_or("not an L2BM opcode")?;
    let bad = || format!("unknown L2BM opcode `{opcode}`");
    let (head, set) = match rest.split_once('@') {
        Some((h, s)) => (h, Some(s)),
        None => (rest, None),
    };
    let l1bset = || -> Result<L1bSet, String> { set.map(L1bSet::parse).unwrap_or(Ok(L1bSet::ALL)) };
    match head {
        "dars" => return Ok(L2Op::Dars),
        "darw" => return Ok(L2Op::Darw),
        "b" => return Ok(L2Op::Bcast { set: l1bset()? }),
        "b2" => return Ok(L2Op::Bcast2 { set: l1bset()? }),
        "i" => return Ok(L2Op::Imcast { set: l1bset()? }),
        "d" => return Ok(if from_l2 { L2Op::Distrib { set: l1bset()? } } else { L2Op::Gather }),
        "" => {
            let l1b: u8 = set.ok_or_else(bad)?.parse().map_err(|_| bad())?;
            return Ok(L2Op::FromL1b { l1b });
        }
        _ => {}
    }
    if let Some(r) = head.strip_prefix("r2") {
        let (rrn, tail) = Rrn::parse_prefix(r).ok_or_else(bad)?;
        if !tail.is_empty() {
            return Err(bad());
        }
        return Ok(L2Op::Reduce2 { rrn });
    }
    if let Some(r) = head.strip_prefix('r') {
        let (rrn, tail) = Rrn::parse_prefix(r).ok_or_else(bad)?;
        if !tail.is_empty() {
            return Err(bad());
        }
        return Ok(L2Op::Reduce { rrn, set: l1bset()? });
    }
    Err(bad())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn l1b_sets() {
        assert_eq!(L1bSet::parse("0/1").unwrap().mask, 0b11);
        assert_eq!(L1bSet::parse("1/6").unwrap().mask, 0b1010_1010);
        assert_eq!(L1bSet::parse("[0,2,4,6]").unwrap().mask, 0b0101_0101);
        assert_eq!(L1bSet::parse("[0,2,4,6]").unwrap().immode, 6);
        assert_eq!(L1bSet::parse("5").unwrap().mask, 0b10_0000);
    }

    #[test]
    fn opcodes() {
        assert_eq!(parse_l1_opcode("l1bmm@3", false).unwrap(), L1Op::Mwrite { mab: 3 });
        assert_eq!(parse_l1_opcode("l1bmd-1", false).unwrap(), L1Op::Gather { mabdiff: -1 });
        assert_eq!(parse_l1_opcode("l1bmd+1", true).unwrap(), L1Op::Distrib { mabdiff: 1 });
        assert!(matches!(parse_l1_opcode("l1bmrffaddr", false).unwrap(), L1Op::Reduce { round: true, .. }));
        assert!(matches!(parse_l1_opcode("l1bmr4dfadd", false).unwrap(), L1Op::Reduce4 { round: false, .. }));
        assert_eq!(parse_l2_opcode("l2bm@1", false).unwrap(), L2Op::FromL1b { l1b: 1 });
        assert!(matches!(parse_l2_opcode("l2bmrdfadd@[0,4]", false).unwrap(), L2Op::Reduce { .. }));
        assert!(matches!(parse_l2_opcode("l2bmd", true).unwrap(), L2Op::Distrib { .. }));
        assert_eq!(parse_l2_opcode("l2bmd", false).unwrap(), L2Op::Gather);
    }
}
