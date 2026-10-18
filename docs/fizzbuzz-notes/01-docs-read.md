# 01 — MN-Core ドキュメント読破記録

対象: worktree 内の MN-Core 2 ドキュメント一式（短縮作業着手前の必須読破として実施）

## 読了範囲と方法

- `judge/sdm/sdm.txt` 全 5850 行（本人が offset 分割で全チャンク読了）
- `docs/mncore_llm/` 全 344 ページ（README 記載と一致）
  - chapters: ch01 6 + ch02 4 + ch03 178 + ch04 9
  - topics: 144（ja-hiragana 1, ja-kanji 22, ja-katakana 15, latin-ae 16, latin-fj 9,
    latin-ko 33, latin-pt 16, latin-uz 8, num 6, other 18）
  - ch01/ch02/ch04 は本人が全ファイル読了。ch03 と topics は並列サブエージェントで全ファイル読了
    （カバレッジ: 49/49, 33/33, 36/36, 63/63, 38/38, 58/58, 48/48 = 325/325）
  - `indexes/chapter_index.md` `indexes/topic_index.md` 読了（JSON 索引は機械生成の参照用）
- judge 同梱: `judge/README.md`, `judge-py/mncore2_emuenv/{tutorial.md, README.md, Changelog.md}`
- `docs/shortening_techniques.md` 全 127 行

## 詳細ノート（読破の成果物）

- `docs-notes/ch03-3.1-3.5.md`（文/数値/タグ/制御文/MV命令文）
- `docs-notes/ch03-3.6.1-3.6.3.md`（オペランド/マスク/ハザード）
- `docs-notes/ch03-3.6.4-3.6.8.md`（並列実行条件/nop/L2BM/L1BM）
- `docs-notes/ch03-3.6.9-3.7.md`（MAU/行列レジスタ/ALU/wait/サンプル）
- `docs-notes/topics-ja.md`（judge 仕様・tips・チュートリアル・ローカル環境）
- `docs-notes/topics-latin-afk.md`（Challenge/judge改造/Flat/Auto stride/assemble3）
- `docs-notes/topics-latin-pt-uz-num-other.md`（オペランド/レイアウト/1PE実行）

## 短縮に直結する確定事実

- score = `j + m`（flat）。1 命令式 = 1 語、`nop/<n>` = n 語。
  `;` で同一行に束ねても 1 語。`d get/set`・コメント・空行はカウント外。
- 1 行に同居できるのはグループ単位で 1 命令まで:
  ALU / MAU-calc / mwrite / mread / L1B / L2B / MV。MAU は calc/mwrite/mread のうち 2 グループまで。
- `nop` は行を占有（wait 以外と同時発行不可）。`noforward` は他命令と同時発行可。
- forwarding（`$aluf/$mauf/$lbf/$mreadf`）は「直前ステップ（nop/noforward を除く）」の出力のみ。
- ハザード（短縮で効くもの）: LM 書込後 2 step 読不可、GRF/T 1 step、
  PE→L1BM 後 L1BM→PE は 2 step、PE→L1BM 後 L1BM→L2BM は 10 cycle（3 step で安全）、
  L1BM→L2BM 後 L2BM 読み MV は 1 step。
- `d set` を残すと Score invalid。`d get` は提出時トリム（ローカル検証には使える）。
- judge ローカル実行は約 1.2 秒/testcase（高速な反復が可能）。

## ベースライン（変更前）

- `attempts/baseline-93.vsm` に保存。`ACCEPTED score=93 j=91 m=2 bytes=3054`。
