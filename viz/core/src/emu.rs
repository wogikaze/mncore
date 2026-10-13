//! Runs the official assembler and emulator, for differential testing.
//!
//! The binaries live in `judge/judge-py/mncore2_emuenv/` (fetched by `setup_judge.sh`, not in git).
//! Set `MNCORE_EMU_DIR` to use another location.

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;

pub fn emu_dir() -> PathBuf {
    match std::env::var_os("MNCORE_EMU_DIR") {
        Some(d) => PathBuf::from(d),
        None => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../judge/judge-py/mncore2_emuenv"),
    }
}

pub fn available() -> bool {
    emu_dir().join("gpfn3_package_main").exists()
}

/// Assembles and runs `vsm`, returning the debug dump (the output of `d get`).
pub fn run(vsm: &str) -> Result<String, String> {
    let dir = tempdir();
    let vsm_path = dir.join("in.vsm");
    let asm_path = dir.join("in.asm");
    let dmp_path = dir.join("out.dmp");
    std::fs::write(&vsm_path, vsm).map_err(|e| e.to_string())?;

    let asm = Command::new(emu_dir().join("assemble3"))
        .arg(&vsm_path)
        .output()
        .map_err(|e| e.to_string())?;
    if !asm.status.success() {
        return Err(format!("assemble3 failed:\n{}", String::from_utf8_lossy(&asm.stderr)));
    }
    std::fs::write(&asm_path, &asm.stdout).map_err(|e| e.to_string())?;

    // The judge runs the emulator with zero-initialized DRAM and PDM.
    let emu = Command::new(emu_dir().join("gpfn3_package_main"))
        .arg("--offchip-memory-init")
        .arg("zero")
        .arg("-i")
        .arg(&asm_path)
        .arg("-d")
        .arg(&dmp_path)
        .output()
        .map_err(|e| e.to_string())?;
    if !emu.status.success() {
        return Err(format!("emulator failed:\n{}", String::from_utf8_lossy(&emu.stderr)));
    }
    let dump = std::fs::read_to_string(&dmp_path).map_err(|e| e.to_string())?;
    let _ = std::fs::remove_dir_all(&dir);
    Ok(dump)
}

fn tempdir() -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static SEQ: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "mncore-sim-{}-{}",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Key of one dumped value: memory name as printed by the emulator (`LM0`, `GREG1`, `TREG`,
/// `OMR`, ...), PE path (`n0c0b0m0p0`), and address. The address is the word address for
/// LM/GRF, the long word index for T (2 * cycle + k, as read by `d get $llt`), and `entry * 4 + cycle` for the mask register.
pub type DumpKey = (String, String, u32);

/// Parses `d get` / `d get[dfh]` output into a map from location to long word value
/// (or 4-bit flags for the mask register).
pub fn parse_dump(dump: &str) -> HashMap<DumpKey, u64> {
    let mut out = HashMap::new();
    let mut omr_seen: HashMap<(String, u32), u32> = HashMap::new();
    for line in dump.lines() {
        let Some(rest) = line.strip_prefix("DEBUG-") else { continue };
        let Some((mem, rest)) = rest.split_once('(') else { continue };
        let Some((loc, rest)) = rest.split_once(')') else { continue };
        let Some((pe, addr)) = loc.split_once(',') else { continue };
        let Ok(addr) = addr.parse::<u32>() else { continue };
        let rest = rest.trim_start_matches(':');
        let val = if let Some(m) = rest.strip_prefix("Mask{") {
            let n: String = m.chars().take_while(|c| c.is_ascii_digit()).collect();
            let Ok(v) = n.parse::<u64>() else { continue };
            let k = omr_seen.entry((pe.to_string(), addr)).or_insert(0);
            let cycle = *k % 4;
            *k += 1;
            out.insert((mem.to_string(), pe.to_string(), addr * 4 + cycle), v);
            continue;
        } else if rest.matches("v:0x").count() > 1 {
            // Two long word access prints both long words on one line. For T the address is
            // the cycle, so the long words are numbered 2 * cycle and 2 * cycle + 1.
            for (k, v) in rest.split("v:0x").skip(1).enumerate() {
                let hex: String = v.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
                let Ok(val) = u64::from_str_radix(&hex, 16) else { continue };
                let a = if mem == "TREG" { addr * 2 + k as u32 } else { addr + 2 * k as u32 };
                out.insert((mem.to_string(), pe.to_string(), a), val);
            }
            continue;
        } else if let Some(v) = rest.split("v:0x").nth(1) {
            v
        } else if let Some(v) = rest.split("(0x").nth(1) {
            v
        } else {
            continue;
        };
        let hex: String = val.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
        let Ok(val) = u64::from_str_radix(&hex, 16) else { continue };
        out.insert((mem.to_string(), pe.to_string(), addr), val);
    }
    out
}

/// Assembles VSM with the official assembler in the judge's flat instruction mode.
pub fn assemble(vsm: &str) -> Result<String, String> {
    let dir = tempdir();
    let vsm_path = dir.join("in.vsm");
    std::fs::write(&vsm_path, vsm).map_err(|e| e.to_string())?;
    let asm = Command::new(emu_dir().join("assemble3"))
        .arg("--instruction-mode")
        .arg("flat")
        .arg(&vsm_path)
        .output()
        .map_err(|e| e.to_string())?;
    let _ = std::fs::remove_dir_all(&dir);
    if !asm.status.success() {
        return Err(format!("assemble3 failed:\n{}", String::from_utf8_lossy(&asm.stderr)));
    }
    Ok(String::from_utf8_lossy(&asm.stdout).into_owned())
}

/// Runs already assembled input with the emulator and returns the debug dump.
pub fn run_asm(asm: &str) -> Result<String, String> {
    let dir = tempdir();
    let asm_path = dir.join("in.asm");
    let dmp_path = dir.join("out.dmp");
    std::fs::write(&asm_path, asm).map_err(|e| e.to_string())?;
    // The judge runs the emulator with zero-initialized DRAM and PDM.
    let emu = Command::new(emu_dir().join("gpfn3_package_main"))
        .arg("--offchip-memory-init")
        .arg("zero")
        .arg("-i")
        .arg(&asm_path)
        .arg("-d")
        .arg(&dmp_path)
        .output()
        .map_err(|e| e.to_string())?;
    if !emu.status.success() {
        return Err(format!("emulator failed:\n{}", String::from_utf8_lossy(&emu.stderr)));
    }
    let dump = std::fs::read_to_string(&dmp_path).map_err(|e| e.to_string())?;
    let _ = std::fs::remove_dir_all(&dir);
    Ok(dump)
}
