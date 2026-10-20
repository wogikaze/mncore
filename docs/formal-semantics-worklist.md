# MN-Core形式意味論の作業リスト

## 方針

- `legal` は広く取る。拒否や実行時エラーは `step` の失敗として表す。
- 意味論は、全命令を対象にする「足跡」と、値を扱う意味論に分ける。
- 足跡は各命令の読み書き範囲を記録する。全命令について定義する。
- 下限証明に使う値の意味論は、実際の動作を含む健全な抽象として全演算器に与える。上限証明には、必要な命令の厳密な意味論を実装する。
- まず Welcome の正しさと最適性を証明する。後続問題で必要になった厳密な意味論だけを追加する。
- Lean の外で解を探索し、Lean では探索結果を検証する。

## 0. 進め方

### 0-1. 開発中の検証

開発中は変更したモジュールに対して `lake build <変更したモジュール>` だけを実行する。`check.py` はコミット直前に実行する。

### 0-2. コミット単位

成果のまとまりごとにコミットする。コミット方法は `AGENTS.md` に従う。

### 0-3. 有限性と範囲付け

有限性と範囲付けの作業は凍結する。既存の定理は維持し、新しい定理は追加しない。

### 0-4. CIの失敗を意味論の失敗と混同しない

2026-10-17時点でGitHub Actionsは失敗している。Lean監査は `judge/judge-py/judge.py` が無く `check.py` が停止し、Baselineは `setup_judge.sh` が取得した122バイトの応答をZIPとして展開できず停止する。どちらも意味論の検証まで到達していないため、CI結果を証明の成否として扱わない。judge取得を復旧した後にCIを再評価する。

## 1. Phase 2の監査結果

2026-10-18の現物確認では、ここに列挙していたPhase 2の変更作業はすでに実装済みだった。
この節は未実施タスクではなく、確認済みの状態記録として扱う。

- `ProgramLegality.lean` の `partialMachine.legal` は常に `True`。
- `normalizedExecutableLine_legal` が、正規化成功後の実行行を広い候補領域へ含める。
- issue/hazard 条件は `boundedIssueMachine` に分離され、候補列挙の合法条件には使われていない。
- 有限carrier/envelope方式は冒頭の方針どおり凍結済み。`coverage.json` も有限性作業を `frozen` と記録している。
- したがって、旧項目1-1〜1-4を再実装しない。残る主課題はPhase 3の実機意味論、健全な抽象、初期状態、各問題の上限・下限証明である。

### 監査で残った未完了

- 正規化成功から実際のparser/assembler出力範囲までを結ぶ完全な対応証明は未完了。
- WelcomeはLM1全出力の最終readback、一般1行以下の下限、公式emulator差分が未完了。
- Convert Endianは一般VSM parser、lowered line全体のissue/hazard込み実行、2行下限が未完了。
- 行列MAU D/F/G/H × `fma`/`mul`/`add`/`passa` は `WholeMachineStep.lean` のissue-line遷移に接続済み。MAB単位のsource read、block-float dot、accumulator alignment、PE bus/MAUF flags、mask/flush、poison付きdestination write、MAUF forwardingを実装している。
- Rust parserとのsource arity照合も済み、matrix `add`/`passa` は2 source。Rust `compute_mat` は全kindでmatrix operandとvector operandを読み、`fma` はさらにaccumulatorを読む。
- `ParsedIntegerStep.lean` の `parsedMatrixMAUElement` / `parsedMatrixMAUProductRow?` はD/F/G/Hの物理stride/lane配置をRust `mat_get` に合わせ、F precisionのdot列は0,2,4,6を選ぶ。4精度のelement layout、shape/dot幅の補題があり、Lean build済み。
- `RRN.lean` の `matrixBlockFloatDot` / `matrixBlockFloatFma` はRust `bf_dot` のblock仮数decode、partial-product補正、共通指数grid、exact/fallback加算、accumulator alignmentをモデル化する。半精度BF積と単精度accumulatorの具体readbackを `decide` で証明済み。
- 未完了はRust `compute_mat` との命令・精度・境界値別差分照合、および照合結果のevidence/coverage記録。コード接続済みであることは参照機一致の証明を意味しない。

以下の旧Phase 2詳細は、監査根拠を追うために残す。

<!-- Historical Phase 2 checklist; items below are complete or frozen per audit above. -->

## 1a. Phase 2の実装記録（完了）

### 1-1. `partialMachine.legal` を広げる

`normalizeForSubmission?` が成功することだけを `legal` の条件にする。`programIssueAndHazardLegal` は条件から外し、同時発行違反やハザードは後段の `step` が失敗するようにする。

完了条件は、抜き取り実験だけを根拠にした制約が `legal` に残っていないこと。

### 1-2. `legal` の広さを定理にする

正規化できるソースはすべて `legal` を満たす、という形の定理を示す。これにより、`legal` が狭いために解を見落とす可能性を構造上なくす。

### 1-3. 有限な命令列の経路を選ぶ

`encodedUniverseMachine` と `InstructionLine` の範囲を使う経路を比較し、残す経路を決める。採用しない経路は README に使用しない旨を記す。

### 1-4. Phase 2の状態を記録する

`coverage.json` と README の記述を実態に合わせて更新する。有限性は列挙の器として達成済みであり、下限証明には記号的な証明書を使うことを明記する。

## 2. Phase 3の意味論

### 2-1. 実機状態を定義する

既存の `ParsedIntegerStep` のレジスタ状態を土台に、機械の `State` を定義する。状態には次を含める。

- 全PEの5バンクのPEメモリとOMR
- `aluf`、`mauf`、`lbf`、`mreadf` の各フォワーディングレジスタと有効状態
- L1BM、L2BM、DRAM
- マスク制御状態
- ハザードの時計

PE/L1BMの外形はRust実装と一致させる。Rustの`GROUPS=4`,
`L2B_PER_GROUP=2`, `L1B_PER_L2B=8`, `MAB_PER_L1B=16`,
`PE_PER_MAB=4`から4096 PE、64 L1BMとなる。

### 2-2. 全命令の足跡を定義する

`footprint : InstructionLine → (読む場所, 書く場所)` を定義する。足跡はオペランド構文から決まり、命令の値を計算できるかどうかに依存させない。

任意の命令について `step` が成功した場合、状態の変化は足跡に記録された書き込み範囲内に限られることを証明する。値が未解釈の命令にも成り立つ定理にする。

### 2-3. 実行時の失敗を `step` に含める

同時発行の違反は `Issue.check` で検出する。PEとblockのハザードは既存チェッカーで検出する。MAU disabled など、無効なフォワーディングレジスタ読み出しも失敗にする。

既存チェッカーの健全性定理を再利用し、各条件の違反が `step` の失敗になることを示す。

### 2-4. 下限用の健全な値の抽象と上限用の厳密な意味論を作る

下限証明では、値が未定義の命令を `unknown` のまま扱わない。全演算器に、実際の動作を含む健全な抽象を定義する。抽象が粗い場合は下限証明が通らないことがあるが、実際には可能な解を誤って排除しない。

抽象は少なくとも次を追跡する。

- **定数の抽象**：入力に依存しない結果を任意の定数として表す。`fma(C,C,C)` など、定数から作られる特殊な値も含める。定数が何行目に、どの同時発行枠で生成され、どのレジスタに置かれるかも記録する。
- **依存の抽象**：出力の各ビットまたは各レーンが、入力のどのビットに依存しうるかを追う。例えば `sbsl` のレーン `i` は、`a` のレーン `i` と `b` のシフト量ビットに依存する。

上限証明には、必要な命令だけ厳密な値の意味論を実装する。Welcome では既存の整数ALUとLM1への書き込み経路を扱い、2語幅・4語幅のアクセスにおける `wide_access_and_lsb_passthrough` も定義する。

### 2-5. 初期状態を確定する

judgeの実際の動作と問題文を調べ、LM1など未初期化領域を0とするか、任意の値とするか決める。その仕様を `State` の初期状態に反映する。

### 2-6. 単精度FMAをビット単位で実装する

MN-Coreの単精度FMAをLeanのカーネル内で評価できる形で実装する。Leanの `Float` はネイティブ実装のためカーネル内で評価できないので使わない。

`fma` のビット単位の結果をLeanで証明し、公式エミュレータ `gpfn3` と差分照合する。定数入力の具体計算は `decide` または `rfl` で検証できる形にする。

## 3. Welcomeを縦に解く

### 3-1. 問題仕様を記述する

入力はLM0の `$m0..$m15`、出力はLM1の `$n0..$n15` とし、各出力を対応する入力に1を加えた値とする。

全入力値域を対象にする仕様と、テストケースの値域だけを対象にする仕様を区別する。テストケースが読む `n0c0b0m0p0` の扱いも明記する。

### 3-2. 2行解の正しさを示す

`answer.vsm` の次の2行が、定義した機械の `step` で仕様を満たすことを証明する。

```vsm
iinc $lm0v $ln0v
iinc $lm8v $ln8v
```

### 3-3. 1行以下では解けないことを示す

`SymbolicBoundCertificate` を使い、0行と1行を分けて証明する。

- 0行ではLM1への書き込みがないため、足跡の定理から不正解と結論する。
- 1行では、同時発行規則によりLM1を書ける書き込み元は1つに限られる。その書き込み元が16語すべてを入力+1にできないことを示す。
- ALUは64ビットバスなので1サイクルに処理できるのは2語であり、16語には届かない。
- MAUの `passa` やblock転送など、より広い書き込み経路については、値の抽象を使って入力+1を生成できないことを示す。

完了条件は、`PlusOne.lean` の限定モデルを実機の状態と意味論に置き換え、実機モデル上で `Optimal` を証明すること。`audit.json` でWelcomeを `proven` にする。

### 3-4. 公式エミュレータと差分照合する

2-4で実装した値の意味論を、既存の `check_*_reference.py` と同じ方式で公式エミュレータと照合する。

### 3-5. 下限証明の失敗から探索条件を取り出す

下限証明が失敗した場合、反証できなかった場合分けから、必要な定数や依存関係を特定する。例えば、ある行で任意定数 `k1` を使ってシフトし、次の行で任意定数 `k2` を使ってレーンごとにシフトする場合、`k1` と `k2` をその行数と同時発行枠で生成できるかを条件として取り出す。

その条件をRustシミュレータ（`viz/core`）で探索する。`imm` の値と同時発行で得られる派生値を調べ、見つかった解をLeanの厳密な意味論で上限として検証する。探索自体はLeanの外で行う。

## 4. Convert Endianの3行解と2行下限を検証する

Welcomeの次に扱うConvert Endianでは、整数と浮動小数点をまたぐ3行解の上限と2行下限を次の条件で検証する。

### 4-1. 3行解の正しさをビット単位で示す

使う命令は `imm`、32ビットレーンの `ibsl`、単精度FMAの `fvfma`、`mauf` のビットからレーンごとのシフト量を取る `sbsl` とする。

2行目の `fvfma` が読む `aluf` は1行目の `imm` の結果である。同じ行に発行した `ibsl` の結果ではない。この読み出し先行の規則を形式化する。

アドレス `$n[1,0,3,2]` のフラット指定における並び順も定義し、出力との対応を証明する。

FMAの入力が定数なら、必要な浮動小数点計算は具体例に限られる。2-6のビット単位実装を使い、`decide` または `rfl` で検証する。全64ビット入力に対する一般性は、総当たりではなく `BitVec` の補題で示す。`bv_decide` と `Lean.ofReduceBool` には依存しない。

### 4-2. 2行では解けないことを示す

`unknown` を下限証明に残さず、2-4の定数抽象と依存抽象で全命令を覆う。

定数抽象は `fma(C,C,C)` が生成する特殊な定数も許し、生成に必要な行、同時発行枠、レジスタ配置を記録する。依存抽象は各ビットと各レーンの入力依存を追跡する。抽象の範囲内に候補が残った場合は、その候補を3-5の探索条件にする。

この証明は候補を反証する。3行解そのものの発見はRustシミュレータに任せ、見つかった解の正しさは厳密なLean意味論で検証する。

## 5. Welcome以降の横展開

### 5-1. 対象問題の順序

Welcomeの次はConvert Endianを扱う。簡単な問題から順に進め、1.a-bなど少ない行数で解ける問題も対象にする。

### 5-2. 必要な厳密意味論を追加する

各問題で上限証明に必要になった演算器や転送経路の厳密な値意味論だけを追加する。全命令の下限用抽象と足跡は維持する。

### 5-3. 下限証明の共通補題を整える

繰り返し使う足跡、書き込み容量、演算器ごとの値制約を共通補題にまとめる。

## 実施順

`0 → 1 → 2-1 → 2-2 → 2-3 → 2-5 → 3-1 → 2-4 → 2-6 → 3-2 → 3-3 → 3-4 → 3-5 → 4 → 5`

2-6は、定数FMAを含む候補を下限抽象が正しく包含するため、Welcomeの最適性証明を閉じる前に実装する。3行解のビット単位の証明は、対応する問題の上限検証に進む段階で行う。

## 難所

1行の同時発行で、ALU以外の幅広い書き込み経路が入力+1を作れないことを示す部分がWelcomeの下限証明で難しい。MAUやblock転送の値を `unknown` とすると結論できず、人手の命令分類だけではFMAから特殊な定数を作る場合を見落としうる。

全命令の健全な抽象で候補を広く含め、証明できない場合分けを具体的な探索条件に変える。探索はRustで行い、得られた解は厳密なLean意味論で検証する。

## 次に実装する作業

古い「実施順」は当初計画であり、現時点の順序としては使わない。現在の最優先は、coverage上の未実装領域をwhole-state遷移へ接続し、各接続の参照動作を検証すること。

1. 行列MAUをRust `compute_mat` と照合する。D/F/G/H × `fma`/`mul`/`add`/`passa`、`u/d` row mask、round出力、block-float poison、source forwarding、MAUF flagsを命令・精度ごとに検証する。
2. DAR/DARBUFと `l2bmdars` / `l2bmdarw`、全MV modeの間接DRAM address resolverをwhole-state遷移に接続済み。`nd=N` の再利用単位は公式PDFの16-longwordアクセスで表し、例示 `nd4` と省略時のentry再利用をLean定理化した。MV発行時は元メモリとDARから書き込み列を採取して状態キューに保留し、waitは指定タグの転送だけを完了し、プログラム終端で残りをflushする。発行時の採取結果を既存同期MV意味論でcommitした状態と一致させる定理を追加。SDM 3.6.13に合わせ、wait中は後続PE/MV行を発行しない。さらに `ScheduledEvent.issue` / `completeMv` による明示的スケジュール実行器を追加し、任意の保留タグ完了順をイベント列で表現可能にした。正確な遅延、優先度からイベント順への制約、waitなし実行の全スケジュール網羅性は未完了。DAR/MV間接のRust executorが未実装のため、参照binaryによる差分確認は未完了。
3. `coverage.json` のPE/L1BM/L2BM/MV datapath-only範囲を受理命令ごとに分解し、WholeMachineStepの `.unknown` 到達条件と照合して、未接続のaccepted formを減らす。
4. hazard/disabled-forwarding failure、VSM parserからfixed encodingへの対応、公式binary conformanceを接続・証明する。
5. 各範囲で `unknown` が消えた条件と残る条件をcoverageへ反映し、最終的に全命令の足跡・健全な抽象・必要な厳密意味論を揃える。
