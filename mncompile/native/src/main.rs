//! Evaluation server for the compiler's search loop.
//!
//! Reads one JSON request per line on stdin and writes one JSON response per line:
//!   {"prefix": "...", "program": "...", "suffix": "..."}  (prefix/suffix may be replaced by
//!   "prefix_id"/"suffix_id" after registering them with {"register": id, "text": "..."}).
//! The response has the instruction word count of the program, an error (if any) with the
//! failing part and line, and the values printed by `d get` statements.

use std::collections::HashMap;
use std::io::{BufRead, Write};

use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};
use serde::Deserialize;
use serde_json::{Value, json};

#[derive(Deserialize, Default)]
struct Request {
    register: Option<String>,
    text: Option<String>,
    prefix: Option<String>,
    prefix_id: Option<String>,
    program: Option<String>,
    suffix: Option<String>,
    suffix_id: Option<String>,
}

fn main() {
    let stdin = std::io::stdin();
    let mut out = std::io::BufWriter::new(std::io::stdout());
    let mut registered: HashMap<String, Vec<(usize, Line)>> = HashMap::new();
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        if line.trim().is_empty() {
            continue;
        }
        let response = match serde_json::from_str::<Request>(&line) {
            Ok(req) => handle(req, &mut registered),
            Err(e) => json!({"error": format!("bad request: {e}")}),
        };
        writeln!(out, "{}", response).unwrap();
        out.flush().unwrap();
    }
}

fn parse_part(text: &str) -> Result<Vec<(usize, Line)>, String> {
    vsm::parse(text).map_err(|e| e.to_string())
}

fn handle(req: Request, registered: &mut HashMap<String, Vec<(usize, Line)>>) -> Value {
    if let Some(id) = req.register {
        return match parse_part(req.text.as_deref().unwrap_or("")) {
            Ok(lines) => {
                registered.insert(id, lines);
                json!({"ok": true})
            }
            Err(e) => json!({"error": e, "part": "register"}),
        };
    }
    let get = |text: &Option<String>, id: &Option<String>| -> Result<Vec<(usize, Line)>, String> {
        if let Some(id) = id {
            return registered.get(id).cloned().ok_or_else(|| format!("unknown id {id}"));
        }
        parse_part(text.as_deref().unwrap_or(""))
    };
    let prefix = match get(&req.prefix, &req.prefix_id) {
        Ok(p) => p,
        Err(e) => return json!({"error": e, "part": "prefix"}),
    };
    let suffix = match get(&req.suffix, &req.suffix_id) {
        Ok(p) => p,
        Err(e) => return json!({"error": e, "part": "suffix"}),
    };
    let program = match parse_part(req.program.as_deref().unwrap_or("")) {
        Ok(p) => p,
        Err(e) => return json!({"error": e, "part": "program"}),
    };
    let words: u64 = program.iter().map(|(_, l)| l.words() as u64).sum();
    let mut sim = Sim::new();
    for (part, lines) in [("prefix", &prefix), ("program", &program), ("suffix", &suffix)] {
        if let Err(e) = sim.run(lines) {
            return json!({"error": e.msg, "part": part, "line": e.line, "words": words});
        }
    }
    let dump: Vec<Value> = sim
        .dump
        .iter()
        .map(|((mem, pe, addr), v)| json!([mem, pe, addr, format!("{v:016x}")]))
        .collect();
    json!({"words": words, "dump": dump})
}
