# proofs/

このディレクトリには **Lean でカーネル検証された証明だけ**を置く。

規約:
- 証明は `proofs_lean/` の Lean プロジェクトに属し、`python3 proofs_lean/scripts/check.py`
  （クリーンビルド、`sorry`/独自axiom/`native_decide` の拒否、カーネル依存検査）を通ること。
- Python・SAT/CP-SAT・総当たり・エミュレータ実測による解析は **証明ではない**。
  それらは `research/preliminary/` に置き、文書冒頭に「これは Lean 証明ではない」と明記する。
- 「証明済み」と書けるのは、上記 check を通った定理だけ。

現状: このディレクトリに Lean 証明はまだ無い（`proofs_lean/` 側の作業が進行中）。
