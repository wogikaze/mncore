# challenge-mid: 23.fizzbuzz-pe / 21.hello-world / 18.inversion-small / 14.mat-sq / 9.transpose-addr

結論: 5 問とも短くならなかった。
ただし `judge.py --dirty`（メモリをゼロで初期化しない）では、記録解のうち 18.inversion-small と 9.transpose-addr が不合格になる。
9.transpose-addr には、clean と dirty の両方で ACCEPTED になる 10 語版 `9.transpose-addr/dirty10.vsm` を作った（`ACCEPTED!! score=10 j=10 m=0 bytes=735`、golfcheck も OK）。
18.inversion-small は、dirty でも通る 9 語以下の解を作れていない。
（Challenge のサイトは、ローカルの --dirty で落ちる解も Accepted にしている。small-alu/REPORT.md の注を参照。）

| 問題 | 記録 | 最良 | judge（clean / dirty） |
|---|---:|---:|---|
| 23.fizzbuzz-pe | 9 | 9（記録解） | ACCEPTED / ACCEPTED（全範囲テストケースでも） |
| 21.hello-world | 9 | 9（記録解） | ACCEPTED score=9 j=8 m=1 / ACCEPTED |
| 18.inversion-small | 9 | dirty で通る解なし | 記録解: ACCEPTED / 64 値すべて不一致 |
| 14.mat-sq | 10 | 10（記録解） | ACCEPTED / ACCEPTED |
| 9.transpose-addr | 10 | 10（dirty 対応版） | `dirty10.vsm`: ACCEPTED / ACCEPTED。記録解は dirty で 7 個不一致 |

## 共通の道具
- `probe.py`: 公式アセンブラと公式エミュレータで候補を実行し、任意の `d get` を表示する。
- `asm.py`: アセンブラ検査だけを行う。
- 実測した規則:
  - GRF は、書いたサイクル c に対して次の行のサイクル c+3 以降なら読める（c+2 以前は racy）。
  - 1 行で読めるマスク番地は 1 つだけ。書き込みマスクとゼロフラッシュでも同じ（"conflict one-time mask imr"）。
  - **マスクレジスタへの書き込みには、書き込みマスクが効かない。** `$omr1/$imr2` と `maskk` のどちらでもエントリ全体が上書きされた（`fl2.py`, `fl3.py`）。
  - hv 系 MAU のフラグは半語レーンごとに立つ。fv 系は語単位になる（`fl.py`）。
  - dvpassa の出力 2 長語は (値, 0) になる。

## 23.fizzbuzz-pe（9 語）
- 記録解の動作:
  - imm 1/3 を置き、iadd で A を 1/3 の仮数に足し込み、fvadd で 1/3 を引いて a = A·2^-25 を作る。
  - a に 1/3 と 0.2 をかけ、積の bit3..6 を `iand 0x78` で調べて div3/div5 マスクを作る。
  - ゼロフラッシュ 2 回と 0.2 の減算で div15 マスクを作る。
  - imm 3 つ（BBBB, FFFF, FFFFBBBB）をマスク付きで書く。
  - ALU 欄は 9 行すべて埋まっている（imm 6 + iadd + iand 2）。
- 検証: 1..32768 を一度ずつ置いた全範囲テストケース `full.vsm`（`genfull.py`）を作った。記録解はこれでも clean/dirty とも ACCEPTED。
  - div3 の積は下位 10 ビットが 0 で正確だった。非倍数は下位 2 ビットが必ず非 0 だった（`p1.py`）。
- 試したこと:
  - 出力 imm を 2 つにする案。A の上位半語は常に 0 なので、0000FFFF/(d3) → FFFFBBBB/(上位: d15, 下位: d5) の 2 回で足りる。これで ALU が 8 命令になる。
  - 半語ごとに違うマスク (d15, d5) を、マスクレジスタへのマスク付き書き込みで作る `c8a.vsm`（8 語）を書いた。
  - 結果: アセンブルは通るが、マスク付き書き込みが無視されて 8738 件（3 の倍数の側）が不一致になった。
- 行き止まりの理由:
  - ALU で作る `iand` のフラグは、上位半語にはデータの情報を載せられない（小数部は下位ビットにある）。
  - MAU の符号フラグでは割り切れるかどうかを判定できない。ゼロフラッシュした値は +0 になってフラグ 1 になる（常に「書く」側）。
  - 1 行 1 マスクの制約で、W1 とマスク合成を同じ行に置けない。
  - 定数 0x78 は P の指数ビットと重なるので、他の定数の下位ビットに隠せない。シフトを使う判定も、シフト量に合う定数がない。
  - 0.2 は 1/3 から MAU で作れない。
  - 以上から、ALU 8 命令と鎖の長さ 8 行を同時に満たす配置は見つからなかった。

## 21.hello-world（9 語、j=8 m=1）
- 記録解の動作:
  - 3 つの imm と、dvpassar（倍精度から単精度への変換）で作る 4 語目の上位バイト 0x13 で 13 バイトを用意する。
  - `idec $subpeid` のマスクで PE0 と PE1 に違う長語を置く。
  - hfadd の縮約 2 段（全体で ×128、半語の指数 +0xE00）で値を合わせ、mvp で DRAM に書く。
- 下限の考え:
  - d0 と d1 は同じ l1bmr サイクルの PE0 と PE1 から来る（L1BM と L2BM のどの配置でも同じ）。したがって PE ごとに値を変える必要がある。
  - そのためには固定値オペランドを使う ALU 命令が 1 つ要る。データは 13 バイトなので imm が 3 つ要る。ALU は計 4 命令になる。
  - GRF の 6 サイクル待ちと L1BM→L2BM の 11 サイクル待ちを入れると、j=8 が下限になる。
  - 行列レジスタの転置（dmwrite/dmread）で PE ごとの値を作れば ALU は imm 3 つで済む。しかし mwrite と mread の 2 行が増えて、やはり j=8 になる。

## 18.inversion-small（9 語）
- 記録解の動作:
  - BAR = 2m、T = 2p（packbit）とし、lsub で A[m] − A[m+p+4c−16] を計算する。
  - 0101 マスクで、差の下位 16 ビットを 1.5 の半語の隣に埋め込む。
  - hmfma の丸めで負の個数を数え、l1bmriiadd で 16 MAB 分を足し、l1bmm で LM1 に書く。
- **dirty では 64 値すべて不一致になる。** 原因は次の 3 つ。
  - packbit の y（$ls0）の MSB が初期化されていない。
  - k<0 のレーンが LM0 の 4064..4095 番地（未初期化）を読む。
  - LM1 の上位側を書いていない。
- dirty 対策として試したこと:
  - y を $lm0 にする案は、BAR の書き込みと LM0 の読み出しが衝突する（in_lm0/out_lm0）。
  - 番兵（MSB=1 の値）を置くには 16 長語分の上位語が必要で、1 命令では足りない。
  - 9 語以下で dirty に通る解は作れなかった。

## 14.mat-sq（10 語）
- 記録解の動作:
  - y に生の X^T を 4 行で書き、hbfe した写しを GRF1 に置く。
  - x に bfe(X^T) を 2 行で書き、y を hmread で転置してベクトルを作る。
  - hmmul を 4 行流す。
- 下限: 10 行。
  - LM0 の読み出し帯域で 4 行、LM1 の書き込み帯域で 4 行かかる（hmmul 1 行で 8 長語/PE）。
  - 出力の列を作るには、ベクトル（X の行）の PE 方向の転置が必ず要る。
  - mwrite は 1 行 1 命令である。同じ行列レジスタは 1 行に 1 回しか使えないので、転置用の y と積用の x の 2 面が要る。
  - したがって mwrite が 6 回（y に 4、x に 2）必要になり、x が揃うのは早くても 6 行目になる。

## 9.transpose-addr（10 語）
- 記録解の動作:
  - drelu の性質 (y, x.lo) で長語の対を組み立てる。
  - LM0 から E 行を写す行、O 行を読みつつ O.hi を GRF1 に置く行、単語の書き込みで残りを埋める行を組み合わせる。
- dirty での不合格の原因: 9・10 行目の x の上位長語（s16, s20…）が未初期化なので、relu の符号判定が乱れる。
- 修正（`dirty10.vsm`）:
  - 7・8 行目の dvpassa の書き先を、5・6 行目の lpassa が GRF1 に写した使われていない領域の下位側（s82…, s98…）に変える。
  - 9・10 行目は `$lls[80,…]`, `$lls[96,…]` を読む。
  - これで x.hi に非負の入力値が入る。語数は 10 のまま、clean/dirty とも ACCEPTED。
- 9 語にならない理由:
  - LM1 の書き込みは 1 行に 2 長語/サイクル（8 長語）までで、64 長語には 8 行かかる。
  - 1 行目は LM0 しかデータがなく、1 命令で読める LM0 の領域は 1 つなので、正しい対を作れない（役に立つのは 4 長語まで）。よって 9 行が下限になる。
  - 9 行を実現するには、2〜9 行目がほぼすべて対を書く必要がある。しかし各組 (E, O) で E.lo を上位へ、O.hi を下位へ動かす必要があり、2 長語の写しを作れるのは ALU（passa）だけである。
  - 必要な写し行と MAU の置き先の数を数えると、ALU/MAU だけでは 10 行を割らない。
  - L1BM 経由（l1bmp で 4 番地離れた 2 長語を組む）は、T/BAR の準備と 2 ステップの待ちで間に合わない。

## ファイル
- `probe.py`, `asm.py`
- `23.fizzbuzz-pe/`: `base.vsm`, `full.vsm`（全範囲テストケース）, `genfull.py`, `fb.py`, `chk.py`, `p1.py`, `fl*.py`（フラグとマスクの実測）, `c8a.vsm`（8 語の失敗例）
- `9.transpose-addr/`: `base.vsm`, `dirty10.vsm`（dirty 対応の 10 語、ACCEPTED）
- `21.hello-world/base.vsm`, `14.mat-sq/base.vsm`, `18.inversion-small/base.vsm`
