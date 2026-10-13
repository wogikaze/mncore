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

    let emu = Command::new(emu_dir().join("gpfn3_package_main"))
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

/// Parses lines of plain `d get` output, such as
/// `DEBUG-GREG1(n0c0b0m0p0,6):(f:..., i:{...}, v:0x3F8000013F800001) #d get ...`,
/// into a map from (memory name, PE path, word address) to the long word value.
pub fn parse_dump(dump: &str) -> HashMap<(String, String, u32), u64> {
    let mut out = HashMap::new();
    for line in dump.lines() {
        let Some(rest) = line.strip_prefix("DEBUG-") else { continue };
        let Some((mem, rest)) = rest.split_once('(') else { continue };
        let Some((loc, rest)) = rest.split_once(')') else { continue };
        let Some((pe, addr)) = loc.split_once(',') else { continue };
        let Some(v) = rest.split("v:0x").nth(1) else { continue };
        let hex: String = v.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
        let (Ok(addr), Ok(val)) = (addr.parse::<u32>(), u64::from_str_radix(&hex, 16)) else {
            continue;
        };
        out.insert((mem.to_string(), pe.to_string(), addr), val);
    }
    out
}
