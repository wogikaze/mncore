# 6問の短縮ブリーフ（FizzBuzz 47語の手法を他の問題へ）

対象: `challenge/19.inversion` (31), `27.dram-ul-16-1024` (13), `12.divrow-vec` (29),
`39.matmul-trb-pkg-lmdram-256-1024-16` (29), `challenge/15.contains` (20), `14.exp` (16)。
括弧は記録済み answer.vsm の score (j+m)。どれも記録上の公開 Top と同じか短い（人が詰めた解）。

## 検証
- 高速: `python3 tools/golfcheck.py <problem> cand.vsm` — 公式 assembler（ハザード検査込み）+ ネイティブシミュレータ、
  answer.vsm の出力とビット一致を要求（~0.1 秒）。許容誤差のある問題（14.exp など）で近似を変えた候補は
  ここで落ちるので、その場合は公式 judge で判定する。
- 公式（最終確認に必須）: `python3 problems/run_problem.py <problem> --solution cand.vsm` → `ACCEPTED!! score=...`
- ネイティブシミュレータだけの一致は合格ではない（ハザードを見ない）。

## 並行して動いているもの
`tools/golfsearch.py` が各問題の式の移動・統合・削除（並べ替えだけ）を探索中。結果は
`research/experiments/resched/<name>.vsm` と `logs/<name>.log`。並べ替えだけで縮むものはそちらが見つける。
ここでは**計算方法・置き場所・定数の作り方を変える短縮**を狙う。

## FizzBuzz（93→47語）で実測したハードウェア規則・手法（research/experiments/fable52/slides_prompt.md §6–12）
- imm は宛先を3つまで、MAU は4つまで同時に書ける。1つの値を複数のレジスタファイルに置き、読む側がコピーを選べばポート衝突が消える。
- imm の値は次の行で `$aluf` として直接読める（レジスタを通さない定数）。
- 書き込みは6サイクル後に完了（同番地なら3行後）。`/1000` マスクで定数を書くと2行後に読める。マスクは1行に1種類（`/1000` と `/$imrN` は同居不可）。
- LM は同じ行で読み書き不可、書くと2行読めない。imm は LM0 に触る命令と同じ行に置けない。
- L1BM は 64 の倍数番地。`l1bmd` で置いて3行以上あと、`l1bmm4` の次の行で `$lbf` として読める → 定数の置き場。
- LM0 の空き番地を追加のレジスタファイルとして使える。ALU の fmax は T 間接参照で LM0 を読める。
- マスクを他の定数の下位ビットに埋め込む。手持ちの値から MAU で定数を作る（imm を減らす）。
- 丸め定数 1.5·2^23 など、1つの定数を複数の用途に兼用する。
- 行数の下限は ALU 欄・MAU 欄・依存の鎖ごとに数えると見える（行き止まりの判定に使う）。
- ISA 仕様: `docs/mncore_llm/`。実測した仕様外挙動: `docs/dataflow-viz/NUMERICS.md`。短縮テクニック集: `docs/shortening_techniques.md`。

## 6問の結果から（2026-11-13）
- 並べ替えだけ（golfsearch）では 6 問とも縮まなかった。縮んだのは計算や定数の作り方を変えたときだけ。
- 14.exp（16→14）: マジック数 1.5·2^23+128 で丸めて ffloor/fftoi/fmax/閾値を消した。最後の 2 乗をやめて鎖を 1 段縮めた。
  シフト量を係数の下位ビットに埋め込み、1 回の imm を `$aluf` と GRF0 に兼用した。許容誤差のある問題では、係数をテストケースと密な格子の両方で選び直す。
- 12.divrow-vec（29→28）: `ipassa $mabid $t` で T に MAB 番号を直接入れて imm を 1 つ消し、行の割り当てを変えて鎖を 1 行前に詰めた。
- 縮まなかった問題の限界は、ほぼ「ハザードの待ち（GRF 7 サイクル、LM0 書き込み後 2 行、T の次行読み出し不可、L1BM→L2BM 10 サイクル、L2BM→MV 1 行）」と
  「転送の帯域（l2bmd 1 回 256 長語など）」だった。DRAM 転送が主体の問題は縮みにくい。
- 各問題の REPORT.md（`research/experiments/resched/*/REPORT.md`）に、測ったハザード規則と行き止まりの理由がある。似た構造の問題では先に読む。
