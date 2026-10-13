//! Checks the hazard analysis against the official assembler.
//!
//! Usage: hazard_check <file.vsm>...
//!
//! For every nop line of each (valid) program, removes one step of the nop and asks the
//! assembler whether the result is still valid; the analysis must agree.

use mncore_sim::{emu, hazard, vsm};

fn main() {
    let mut agree = 0;
    let mut disagree = 0;
    for path in std::env::args().skip(1) {
        let src = std::fs::read_to_string(&path).expect("read");
        if emu::assemble(&src).is_err() {
            println!("{path}: skipped (does not assemble)");
            continue;
        }
        let lines = vsm::parse(&src).expect("parse");
        let base = hazard::analyze(&lines);
        if let Some(c) = base.iter().find(|c| c.violated()) {
            println!("{path}: valid program but analysis reports {c:?}");
            disagree += 1;
        }
        let text: Vec<&str> = src.lines().collect();
        for (k, (lineno, line)) in lines.iter().enumerate() {
            let vsm::Line::Nop { count, .. } = line else { continue };
            // Variant with one nop step removed.
            let mut v: Vec<String> = text.iter().map(|s| s.to_string()).collect();
            v[lineno - 1] = if *count > 1 { format!("nop/{}", count - 1) } else { String::new() };
            let vsrc = v.join("\n");
            let official = emu::assemble(&vsrc).is_ok();
            let reasons = hazard::nop_reasons(&lines, &base);
            let needed = reasons.iter().find(|(i, _)| *i == k).map(|(_, r)| !r.is_empty()).unwrap_or(false);
            if official == !needed {
                agree += 1;
            } else {
                disagree += 1;
                let why: Vec<String> = reasons.iter().find(|(i, _)| *i == k).map(|(_, r)| r.iter().map(|c| format!("{} {:?} {:?}@{:?} lines {}->{} dist {} req {}", c.rule, c.kind, c.res, c.addr, lines[c.from_line].0, lines[c.to_line].0, c.distance, c.required)).collect()).unwrap_or_default();
                let err = emu::assemble(&vsrc).err().map(|e| e.lines().find(|l| l.contains("rror") || l.contains("hazard") || l.contains("racy") || l.contains("conflict")).unwrap_or("").to_string()).unwrap_or_default();
                println!("{path}:{lineno}: assembler {} the variant, analysis says {}\n    {}\n    {:?}", if official { "accepts" } else { "rejects" }, if needed { "needed" } else { "removable" }, err, why);
            }
        }
    }
    println!("{agree} agree, {disagree} disagree");
}
