# MN-Core Challenge 解法リファレンス（primenumber blog, 2024-09-26）

このドキュメントは、以下のブログ記事を「最短行数解法のための実践メモ」として要約したものです。

- Source: https://primenumber.hatenadiary.jp/entry/2024/09/26/234205
- Retrieved: 2026-02-19

`[推定]` は、ブログ記述をベースにこのリポジトリ向けに一般化した推論です。

## 1. 最適化対象の前提

- 目標は「正解しつつ行数（score）を最小化」。
- 競技環境は決定的・分岐なしの処理モデルなので、命令並列化とデータ配置が支配的。
- 1行に詰めるには、`PE命令の同時発行条件` と `operand制約` の理解が必須。

関連マニュアル:
- `docs/mncore_llm/chapters/ch03/section-3.6.4__並列実行条件__66b35ffe.md`
- `docs/mncore_llm/chapters/ch03/section-3.6.1.6__m-LM0ベースアドレスレジスタ書き込みを除く__66b35ffe.md`
- `docs/mncore_llm/chapters/ch03/section-3.6.1.8__n-LM1ベースアドレスレジスタ書き込みを除く__66b35ffe.md`

## 2. ブログ由来の重要パターン

### 2.1 「演算」ではなく「データ経路」で縮める

- `ALU/MAU/L1BM` の組み合わせ発行を前提に、1行で複数効果を取る。
- 単純に演算命令を足すより、転送命令を使って「必要な形へ並べ替える」方が短くなるケースがある。

### 2.2 2長語アクセスとフォワーディングの活用

- `ll` オペランドや `passa/fpassa` を使い、1行で取得できる要素数を増やす。
- `[推定]` 「一時保存 + 後段演算」を分割するより、フォワーディング経由で次行に直接流す方が短い。
- フォワーディング種別（`aluf` / `mauf`）は命令ごとに異なるので、実機能確認が必要。

関連マニュアル:
- `docs/mncore_llm/chapters/ch03/section-3.6.1.15__mauf-MAU演算結果フォワーディング__66b35ffe.md`
- `docs/mncore_llm/chapters/ch03/section-3.6.1.16__aluf-ALU演算結果フォワーディング__66b35ffe.md`
- `docs/mncore_llm/chapters/ch03/section-3.6.12.5__passa-コピー命令__66b35fff.md`

### 2.3 ビット表現・数値表現を跨いだ変換

- 演算命令が足りない場合、整数/浮動小数点の表現を利用した変形で代替する。
- 定数生成コスト（`imm` 行数）と演算行数のトレードオフを比較する。
- `[推定]` 「命令が無いから不可」ではなく、等価変形を先に探す。

関連マニュアル:
- `docs/mncore_llm/chapters/ch03/section-3.6.12.3__imm-即値命令__66b35fff.md`
- `docs/mncore_llm/chapters/ch03/section-3.6.12__ALU命令式__66b35fff.md`
- `docs/mncore_llm/chapters/ch04/section-4.3__ベクトル積和演算__66c8adb8.md`

### 2.4 許容誤差を使った近似戦略

- 問題ごとの `atol` を確認し、厳密一致が不要なら近似計算で行数を削る余地がある。
- `[推定]` 近似を使う場合も、符号・ゼロ・飽和境界の失敗ケースを先に潰す。

## 3. このリポジトリでの使い方

### 3.1 検証ループ

1. 候補を `problems/<name>/candidate.vsm` に書く。  
2. ジャッジ実行。  
3. 失敗時は raw 出力で原因（パース/ハザード/値不一致）を切り分ける。  

```bash
python problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm
python problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm --raw-judge-output
```

### 3.2 局所検証（assemble3 + gpfn3_package_main）

- `d set/get` で「実際にどのアドレスが読まれ/書かれるか」を先に確定する。
- `[推定]` 4行化/3行化の可否は、局所アドレッシング実験でほぼ判定できる。

```bash
python docs/scripts/run_assemble3_emu.py \
  --testcase problems/1.a-b/testcase.vsm \
  --solution problems/1.a-b/3lines.vsm
```

## 4. 既存問題への適用メモ

### 4.1 `1.a-b`

- `fpassa + llアクセス + 2段のfvadd分割` で 3 lines が成立。
- 実験メモ: `docs/assembly_experiments_1ab.md`

### 4.2 `2.fmul7`

- `[推定]` 現状観測では `fvmul` 1命令で処理できる float 数に上限があり、`32 float` 全体を埋めるには `fvmul` 複数行が必要。
- さらに係数 `7.0` の供給（`imm`）コストがあり、4行以内の成立条件はかなり厳しい。
- まずは「1命令あたりのカバー範囲」と「同時発行制約」を小実験で固定してから探索する。

---

必要なら次段として、この記事のパターンを「命令別テンプレート（使える入力/出力/forward/典型失敗）」に分解した `docs/challenge_templates.md` を追加する。
