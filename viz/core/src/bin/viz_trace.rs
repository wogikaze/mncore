//! Writes the visualization trace of a problem's solution as JSON.
//!
//! Usage: viz_trace <problem dir> [focus PE index] [solution.vsm] > trace.json

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = std::path::PathBuf::from(args.get(1).expect("usage: viz_trace <problem dir> [pe] [solution]"));
    let pe: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let sol = args.get(3).map(std::path::PathBuf::from).unwrap_or_else(|| dir.join("main.vsm"));
    let testcase = std::fs::read_to_string(dir.join("testcase.vsm")).expect("testcase.vsm");
    let solution = std::fs::read_to_string(sol).expect("solution");
    let mab = pe / 4 * 4;
    let focus: Vec<usize> = (mab..mab + 4).collect();
    match mncore_sim::api::trace(&testcase, &solution, &focus) {
        Ok(t) => println!("{}", serde_json::to_string(&t).unwrap()),
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    }
}
