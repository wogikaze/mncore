//! WebAssembly entry points of the simulator for the visualization site.

use wasm_bindgen::prelude::*;

/// Simulates `solution` inside `testcase` and returns the trace as JSON (see `api::Trace`).
/// The focus is the MAB containing PE `focus_pe` (global PE index).
#[wasm_bindgen]
pub fn trace(testcase: &str, solution: &str, focus_pe: u32) -> Result<String, JsError> {
    let mab = focus_pe as usize / 4 * 4;
    let focus: Vec<usize> = (mab..mab + 4).collect();
    let t = mncore_sim::api::trace(testcase, solution, &focus).map_err(|e| JsError::new(&e))?;
    serde_json::to_string(&t).map_err(|e| JsError::new(&e.to_string()))
}
