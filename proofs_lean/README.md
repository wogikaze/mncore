# MN-Core 最適性証明の再構築

**全ISAに対する最適性証明は現在0/73問。旧 `optimalProven` 判定は撤回した。**
Accepted は正しく実行できる解が存在するという上限の証拠であり、最短性の証拠ではない。
`lake build` 成功や `sorry` がないことだけでも最短性は保証されない。

旧63ファイルは `archive/2026-10-15-arithmetic-claims/` に原文とSHA-256を保存した。
旧定理は実行意味論に結び付いていない数値の検算だった。
旧ラベルを自動昇格していた2つのローカルループ設定も無効化した。

## 完了条件と現在地

目標は全命令・全合法プログラムを覆うモデル上で、73問それぞれに正しい解と最小行数の証明を与えること。
より短い解が見つかった場合は上限を更新して探索・証明を続ける。
既存の参照解が最適であることを前提にしない。

| 必要な証拠 | 状態 |
| --- | --- |
| 旧73件の判定監査、根拠のない最適性主張の撤回 | 実施済み。`audit.json` |
| 合法性、実行、入力域、初期状態、出力仕様、スコアを結ぶ定義 | 汎用基盤を実装。MN-Coreとの接続は未実装 |
| 有限候補宇宙と短縮プログラムの列挙完全性 | 固定幅PE/MV符号語の有限宇宙で達成。全assembler出力との対応は未証明 |
| 候補の反証から下限を導く定理 | `SymbolicBoundCertificate`を含む汎用定理を証明済み。Welcomeへの適用は未実施 |
| 全入力と公式テストケース限定の仕様の区別 | 定義と回帰証明を実装済み |
| 全ISAの合法な命令・オペランド・同時発行のモデル | 未実装。`coverage.json` |
| 全演算器の定数・依存抽象とその健全性 | 汎用symbolic expression基盤を実装。各命令形式との網羅的な接続は未実装 |
| メモリ・通信・丸め・素通り・ハザード・初期化の実行意味論 | 未実装 |
| ゼロコスト制御文を含む構文と、スコア付き命令列の対応証明 | PE/nop/mask directive subsetのloweringとcost保存を証明。完全なVSM接続は未実装 |
| モデルと公式仕様・エミュレータの対応、信頼境界の記録 | 未完了 |
| 73問の正式な仕様とそれぞれの最適性証明 | 未実装、0/73問 |

目標全体は未完了。汎用基盤や小さな例の完成を、MN-Core全ISAの証明完成と数えない。

## 次に進める作業

作業順は `0 → 1 → 2-1 → 2-2 → 2-3 → 2-5 → 2-4a → 2-6 → 3-1 → 3-2 → 3-3 → 3-4 → 3-5 → 4`。
Welcome の後は Convert Endian を縦の2問目にする。有限性・範囲付けの証明は凍結する。

1. Phase 2 を締める。`partialMachine.legal`は正規化済み命令行の全列を許し、issue衝突・PE/block hazard・無効なforwarding読み出しは`step`の失敗へ移す。
   新しい有限性・範囲証明は追加しない。
2. 候補列挙の基盤には`encodedUniverseMachine`を採用する。固定幅PE/MV符号語全体の有限性を使い、`InstructionLine`の範囲付き合法性経路は旧projectionとしてのみ残す。
   assembler sourceから符号語への全域対応は独立した未解決義務として記録する。
3. Phase 2は反映済み。Phase 3では本物のState、全命令footprint、一PEの整数命令部分機械を追加した。全PE状態・forwarding・hazardとstepのframe条件は未接続。
4. 全演算器に定数と入力依存を追跡する健全な抽象を持たせる。`OperatorAbstraction.lean`の汎用式で定数foldingと依存集合の非干渉健全性を証明した。今後は全命令形式・メモリbank・transfer unitをこのAPIへ接続し、網羅性を確認する。厳密な値の意味論は正しさの上限証明に要る部分だけ追加する。
5. 2-6: `SingleFMA.lean`にMN-Core単精度FMAをNat/Int/BitVecだけで実装した。SDMの省略部分積補正、測定済みaccumulator alignment/sticky jam、RNE、zero/infinity正規化を含む。SDM例、tie、overflow、cancellationをkernel reductionで証明。Rust `vfma`との大規模なgpfn3差分は573,440値・不一致0（seed 1234）。Lean関数全体とRustコードの機械的同値証明は未実装で、具体的なkernel計算ケースで照合を追加する。
6. Welcomeは現在、限定された2種類の`iinc`行だけのモデルで証明済み。実VSM行と実状態遷移の接続、全合法1行の下限、公式emulator差分を完了させる。
7. 3-5: 下限証明が失敗した候補から、探索用の条件と具体的な反例を取り出すインターフェースを設計する。Rustシミュレータ向け候補生成器、判定条件、結果の再現記録は未実装。
8. Phase 4はWelcomeの後にConvert Endianを扱う。3行解の整数barrel shift→単精度MAU FMA→整数barrel shift→PE destination selectorの値依存を抽象式にし、合成結果が任意64-bit入力のbyte swapになることを証明した。公式judgeとRust simulatorを含む8値の差分は完了。全メモリアクセス・発行・state transitionへの接続は未実装。
   次題1.a-b（A-B）について、`FloatSubtract.lean`に`fvadd x -y`を単位乗算FMAと符号反転加数として表す式、および定数・依存追跡の健全性、3つの具体例を追加した。64-bit PEバスで上下float laneへ独立に適用する補題もある。`check_single_fma_kernel.py --operation fvsub --vectors 128 --seed 1234 --gpfn-runs 1`でLeanカーネル対Rustの128式、および公式gpfn3対Rustの16,384値を照合し、両方不一致0。これは演算器データパスの小さな証明であり、LeanモデルとRustの全域同値、行列アドレス、issue/state遷移、全入力正当性、2行下限は未完了。
   続いて2.fmul7向けに`FloatMultiply.lean`を追加し、`fvmul`をゼロ加数のFMAとして抽象式へ接続した。7.0を掛ける具体例と定数・依存追跡の健全性を証明し、64-bit PEバスの上位・下位float laneへの独立適用を証明した。`check_single_fma_kernel.py --operation fvmul --vectors 128 --seed 2345 --gpfn-runs 1`でLeanカーネル対Rustの128式、および公式gpfn3対Rustの16,384値を照合し、両方不一致0。命令語配置・4行スケジュール、全域同値、全入力正当性と最適性は未完了。

## 実装した定義

- `Semantics.lean`: 完全な同時発行行から状態への遷移、失敗する実行、スコア、仕様、正しさ、反証入力。
- `PartialSemantics.lean`: 未実装と既知の実行失敗を分離する。
  全命令・全状態で未実装がないことを証明しない限り、完全モデルへ変換できない。
- `PEMachine.lean`: 1つのPEについて、整数register演算の4サイクルを既存のstepperで順次実行する。
  Issue checker拒否は`failure`、MV/待ち制御/未実装演算は`unknown`。全PE状態、forwarding、hazard clock、footprint frameとは未接続。
- `MachineState.lean`: PE 2048個の5バンクregister files/OMR、L1BM 8バンク、L2BM/PDM/DRAM、
  各PEのALUF/MAUF/LBF/MREADF busとvalidity、mask directive、PE context、hazard clockをまとめるState型。
  一般Stateの初期値ポリシーはまだ仮定しない。Welcomeに必要なPE SRAMはRust emulatorの
  `Words::get`が未割当領域をzeroで読むことを確認した。
- `Footprint.lean`: 全`InstructionLine`（PE/nop/MV）と全`ParsedOp`の構文footprintを定義し、
  operand source/destination、functional unit、clockのread/write候補を記録する。
  destination readはmasked writeのpreserve可能性を含む保守的な記録。
  generic operand-storeのframe lemmaはあるが、実際のmachine stepがこのpatch APIだけを使う定理は未接続。
- `ControlNormalization.lean`: データを直接変更せず後続命令の制御状態だけを更新する
  ゼロコスト制御文について、制御状態付き命令列への変換が実行結果とスコアを保存する
  汎用定理。変換後の列を既存の `Machine` 証明基盤に接続した。
  実際のVSMの全ゼロコスト文がこの条件を満たす証明は未実装。
- `Optimality.lean`: 任意の合法・正しいプログラムを量化する下限と最適性。
  証明書の完全性は合法な短縮プログラムの被覆だけを要求し、
  それぞれの候補の不正解の証明を要求する。巨大な候補集合を列挙しない
  Phase 4向けに、候補プログラムの族を述語で表す`SymbolicBoundCertificate`も定義した。
  有限列挙証明書はその特殊ケースへ変換でき、symbolic certificateのsoundnessも証明した。
- `Enumeration.lean`: アルファベット上の命令列を長さ上限まで覆う列挙定理。
  `programsUpToFinset`は有限アルファベットから重複なしの有限候補集合を作る。
  `finiteAlphabetCertificate`は無限の行型からboundごとに切り出した有限carrierにも適用でき、
  `programsUpToFintype`/`fintypeCertificate`は全行型が有限な場合の特例となる。
  各boundの候補列挙完全性を証明したが、MN-Coreの合法な短い行がその有限carrierに入る証明は未接続。
  被覆は合法プログラムに現れる行に対してのみ必要。さらに上限ごとの
  `LegalLinesCoveredBelow` と `legalLinesCostBelow` を定義し、`nop/n`のような
  無限族をコスト上限で有限化する。固定上限の有限被覆が列挙完全性を与える。
  抽象的な`nop/n`モデルでは全上限について有限性を証明した。MN-Core用の候補列挙器には
  `encodedUniverseMachine`の全426-bit PE語／82-bit MV語を選び、有限carrierと短縮列挙完全性を使う。
  旧`InstructionLine`経路のissue・operand-envelope・静的hazard制約付き`Fintype`は定理として保存するが、
  新しい合法性の定義や候補列挙には使わない。全assembler出力との符号語対応と遷移意味論は未接続。
- `evidence/isa-bounds/reference.json`: 公式`assemble3`の3,410個の選択プローブ。
  `nop/0`は受理され0語を出力するため正コストの行からは正規化で除外する。
  `$omr`はu8全域0〜255を走査し1〜15だけが受理される。`$imr`と`maskn`/`maskln`/`masklln`の
  selectorもu8全域を走査し、0〜31だけが受理される。これはRustコメントの「1〜15」と不一致。challenge judgeは
  既定で解答から`d get`/`d set`/`r`記録を実行列から除外する。`--enable-set`で残した
  `d set`はjudgeがscore無効として拒否する。`ParsedLine.normalizeForSubmission_cost`は
  正規化後の命令語コストが各ソース行のsubmission costと一致することを証明し、
  `NormalizedLine.instructionCost_eq_toInstruction_cost`は実行命令型へ変換したコストとの一致も示す。
  `evidence/answer-encoding/reference.json`では全73個のanswer.vsmを公式assemblerで受理し、
  出力1,041語がPE `j` 426-bitを984語、MV `m` 82-bitを57語含むことを記録した。
  境界probeと解答コーパスの両方で観測形式は一致するが、未知の全合法sourceへの一般化は未証明。
  実験範囲外の
  構文・意味や完全網羅を証明するものではない。
  Leanではmask directiveのselectorを`Fin 256`（Rust parserのu8 castと同じ値域）で表し、幅を2または4語、合法selectorを0〜31に制限した有限carrierを証明した。指令適用後も制御状態がその範囲を保つ補題を追加した。
  Leanのmask operator parserが幅2または4だけを生成する補題も追加した。
  selectorはパーサで`% 256`して`Fin 256`に格納する。assemble3の受理範囲である0〜31を別途仮定すれば、完全なmask directive parse結果が有限envelopeに属することもLeanで接続できる。
  `maskln`/`masklln`の境界probeがこれらの幅の字句形式を確認する。
  同じ5個の未知operand fixture（`$qraw`）でRust parserが`Raw`へ落とし、assemble3は命令を出力せず
  異常終了した。これは標本証拠であり、全Raw文字列や未知opcodeの不存在を証明するものではない。
  同時発行のwrite-mask/zero-flush規則について、マニュアル3.6.4の幅一致と3.6.2.1の
  可変entry一致をRustとLeanの`Issue.Legal`に追加した。同幅・同entryは受理され、幅違い・
  entry違い・write maskとzero-flushのentry違いはassemble3で拒否された。
  さらにOMRはPE operandとして単一書込みポートを持ち、異なるissue groupから同じentryまたは
  別entryへ同時に書くlineがassemble3で拒否されることを確認し、RustとLeanに投影・制約を追加した。
  `zero`はLM0/LM1/GRF0/GRF1/T/OMRへ1個ずつ出力する6 destination を受理し、
  各カテゴリ内の重複出力を拒否した。Rust parserはopcodeごとのsource個数で分割後、
  残りの全tokenをdestinationにするため、このassembler観測だけではparser-encoding間の
  一般的なarity健全性を証明しない。追加境界probeでは`zero`の同一category別address出力、
  複数OMR/nowrite出力と`gmwrite`の複数matrix destinationも拒否され、単独`nowrite`は受理された。
  destination上限の証拠はまだ代表opcodeのprobeに留まり、184候補全てへの一般化は未証明。
  Issue.Legal は同一式内の出力bank重複と、`$nowrite`を他destinationと併用する形も拒否する。
  `l2bmdars`と他のL2BM opcodeの7通り、および8 opcode×2 selectorの16通りを追加probeしたが、
  すべて拒否され、マニュアルが記す特殊条件の特定には至っていない。
  `nop; wait i01`は受理され、nopとALUの同時発行は拒否される。MVとPE式を
  同じ行に置く2通りの順序も拒否された。
- `evidence/parser-gap-audit/answers.json`: 問題ディレクトリの全73 `answer.vsm`を
  Rust VSM parserで走査した結果。parse error、`Operand::Raw`、`Op::Other`はいずれも
  0件で、opcode綴りを155種類確認した。1,539個の解答PE式のsource countも記録し、
  最大3であり、destination列が重複しないこともcatalogが検査する。さらにコンパイラ由来の184候補はすべて
  汎用operandを与えたときRust parserに分類された。これは候補の構文解析確認であり、
  assemble3での合法性や全命令の列挙完了を意味しない。
- `check_issue_mirror.py`はRust `parse_expr`のALU/MAU/matrix/other各source分割式と
  Lean `ParsedOp.parserSourceLimit`の対応を検査し、全構造opcodeの最大source数3以下という
  定理の前提がRust parser側とずれた際に失敗する。これは実parser出力の形式的対応証明ではない。
- `evidence/opcode-arity/reference.json`: 184 compiler ALU/MAU/matrix/immediate/zero候補すべてに
  opcode別source数のtemplateを与え、各候補が6以下の固有destination categoryからなる
  maximal templateをassemble3で受理し、同一destinationを追加したoverflowを拒否することを記録した。
  これは選択templateの信頼境界で、オペランド全域を走査せず、L1BM/L2BM、wait/noforward、
  マニュアル上の全opcode inventoryも網羅していない。coverage catalogにもこの範囲を明記する。
- `Issue.lean`の`NormalizedExpr`/`NormalizedMv`/`NormalizedLine`は、表示用の
  `text`を候補同一性から除き、PE式の順序を維持する。未知opcodeはRust parserで
  拒否されるため、Leanの到達可能な`ParsedOp`から文字列付き`other`を除いた。
  SDM 3.6.1.1〜3.6.1.20のPE operand productionsを構造化variantに写し、
  Rustのdiagnostic fallback `Operand::Raw(String)`もLean候補型から外した。
  これはマニュアル文法を閉じた信頼境界とし、公式assemblerの全PE operand受理集合を
  形式証明した主張ではない。
  PEのissue投影と検査が
  正規化で変わらないことを証明した。正規化後の実行命令型ではnop countを正に
  制約し、全命令のコスト正値と`nop/0`除去を証明した。mask directiveは命令行
  でなく、後続状態に畳み込む制御イベントとして残す。未制限の数値フィールドは
  まだ残り、実機命令型の有限性には至っていない。
- judgeの実行フローでは既定設定の`d ...`/`r`記録はassemble後に実行列・スコア列から除去される。
  `--enable-set`で残した`d set`はスコア無効として拒否される。これを根拠に、debug/set/get/DRAM設定行と
  `nop/0`が空列になる提出正規化の補題を追加した。`--enable-get`など診断用の別設定で保持される行の
  実行意味は対象外。
- 同時発行条件は [`ISSUE_AUDIT.md`](ISSUE_AUDIT.md) でSDM 3.6.4と照合した。
  現行checkerはOMR/LBF/BAR出力とマスク読み出しの一部をモデル化したが、
  `l2bmdars`の特殊な同時発行条件など未解決の規則が残る。下限列挙に使える完全な合法性述語ではなく、
  coverageは`partial_datapath_only`のままとする。候補意味論ではissue conflictもstepの失敗として扱う。
- L1B selectorはマニュアルの8バンク構成に合わせ、membership bitmapを`Fin 256`、immodeを`Fin 8`で保持する。
  リスト形式・address/immode形式のparserがこれらの型を直接生成し、mask/immodeの有限carrier証明も維持する。
  PEのBARとmatrix operandのアクセス幅も`Fin 5`で保持し、有限 carrier に反映した。合法envelopeはBARを1/2、matrixを1/2/4に絞る。
  matrix row、L1BM/L2BM address、DAR addressはparserのu32値を`Fin (2^32)`で保持し、L2B selectorはparserのu8値を`Fin 256`で保持する。
  合法envelopeはmatrix row `<16`、L1BM address `<8192`、L2BM address `<32768`、DAR address `<1024`、L2B selector `<8`に絞る。parser値から合法範囲への完全な接続は未証明。
  L1BMの`mwrite`/`m4write`とL2BMの`fromL1b`も、parserが保持する0〜255を`Fin 256`で表す。
  assemblerの有効範囲（MAB `<16`、L1B `<8`）は別の有限envelopeに保持し、受理範囲との接続は未証明としている。
- `FiniteRegion.lean`: assemble3境界プローブを根拠に、width 1/2/4、4つのアドレス`< 4096`、
  `madpe < 4`の`Region` envelopeを有限型へ埋め込み、`Region.inFiniteEnvelope_finite`を証明した。
  `Access.inFiniteEnvelope`ではGRF0/GRF1に限り4 cycle addressを`< 512`に狭め、LM0/LM1の`< 4096`と
  分けた。各bankの容量境界はassemble3記録にあるが、全region cycleと全opcodeの受理集合を結ぶ証明は未完了。
  プローブは`evidence/isa-bounds/reference.json`にある。bank別の合法範囲/alignmentや、
  パーサーからこの上限への一般的な健全性証明は未実装で、PE line alphabet全体の有限性にも未接続。
- `FiniteIssue.lean`: issue projectionが付ける連番IDと同時発行group一意性から、合法なPE行の式数が
  10以下であることを証明した（`projectLine_expression_count_le_ten`）。operandの数値envelopeも定義し、
  有限な要素型上で長さ上限付きListの部分型が有限である補題`listLengthLE_finite`も追加した。
  これは各命令のsource制約とdestination重複制約を得て初めて、式やPE行の有限性に適用できる。
  Rust `parse_expr`の入力prefix分割を`ParsedOp.parserSourceLimit`として写し、ALU入力数、MAUの
  FMA=3/MUL=2/その他、matrix read/write=1、transfer=高々1を記録した。
  `ParsedExpr.sources_length_le_three`はこのarity条件からsource最大3を導くが、
  arbitrary `ParsedExpr` がRust parser出力である証明や、合法なdestination列が重複なしになる証明はまだない。
  184個のopcode候補に対するgeneric-token parseで、Rust parserのsource分割は0件が3候補、
  1件が62候補、2件が104候補、3件が15候補だった。その分布はparser-gap監査と`coverage.json`に記録し、
  正規化でopcode別source arity条件が保存され、そこから3以下が従う補題を追加した。
  これはopcode綴りの網羅やassembler受理性の証明ではない。
  `AssemblerInstructionWord := Sum (BitVec 426) (BitVec 82)`をPE/MV符号語の有限carrierとし、
  その上のcost-bounded program列の有限性、全符号語を含むalphabetによる
  `PartialMachine.shortPrograms_complete`への接続、およびbounded legal-line有限性を証明した。
  このadapterは全bit patternを合法として受け入れる部分モデルで、実MN-Core機械ではない。
  全assembler受理sourceがこのcarrierへ写ることと、符号語のstep意味論が未接続なので、
  `encodedUniverseMachine`はunknown stepのままである。
  operandごとに既存の有限envelopeを要求するsource列のcarrierを追加し、長さ3以下の
  source列全体が有限であることを`ParsedExpr.sourcesInFiniteEnvelope_finite`で証明した。
  destination列は、要素がoperand envelope内でListが`Nodup`なら、その長さが有限operand型のcardinality
  以下になることを示し、有限carrierへ写した。固定の6件上限を全opcodeへ外挿しない形にしたが、
  全合法destination列に`Nodup`を課せる証明はまだない。選択したassemble3 probesでは同一出力categoryの
  重複が拒否されたことだけを確認している。
  opcode本体と同時発行PE行の有限性にはまだ届かない。
  次段階のopcode carrier構成に向け、Leanで既定の`Finite` instanceがない`Char`をUnicode
  code point (`< U+110000`) へ埋め込み有限性を証明し、`ParsedAluName`、`ParsedPrecision`、
  `CalcKind`の有限符号も定義した。ALU引数にはRustのu8範囲を反映し、opcodeのwait tagも
  `Fin 256`で保持するようにした。wait tag、L1/L2 opの既存範囲条件を
  合成した`ParsedOp.inFiniteEnvelope`を定義し、全opcode constructorを有限なタグ付きcarrierへ
  単射で写して`ParsedOp.inFiniteEnvelope_finite`を証明した。parser出力がこの範囲に必ず入る
  ことの証明は別途必要であり、ここでは無制限な`ParsedOp`全体の有限性を主張しない。
  公式assembler probeで観測したPE/MV出力語を`BitVec 426`/`BitVec 82`のsum型に表し、
  その有限性と長さ上限付き符号語列の有限性をLeanで証明した。これはRaw文字列を有限表現へ
  受け止める候補carrierであり、すべてのassembler受理ソースがこの符号語へ写ることの証明ではない。
  これをbounded source列、Nodup destination列、flush maskと組み合わせ、`NormalizedExpr`の有限carrierも
  証明した。source上限3はRust parserのopcode arityから従う。合法destinationがNodupか、全payloadが
  assembler受理範囲内かというenvelope包含証明は残る。
  全ての構造化`ParsedOperand` constructorを有限コードへ写して
  `ParsedOperand.inFiniteEnvelope_finite`を証明した。
  `ParsedMask.entry`をRust parserの保持域に合わせて`Fin 256`にし、assemble3で有効な
  `index.val < 32`の有限部分型へ制限した。PE operand parserは`$imr255`まで保持し`$imr256`を拒否する。
  assemble3では`$imr0..31`が受理され`$imr32`が拒否される一方、OMR entryは別の範囲である。
  parser出力からassemble3の有効範囲への一般証明は未実装。
  OMR indexもRust parserの保持域に合わせて`Fin 256`にし、`1 ≤ entry.val < 16`の有限部分型を
  証明した。PE operand parserは`$omr255`を保持し`$omr256`を拒否する。assemble3の1..15受理・
  16拒否を根拠とするが、parser/assemblerの受理集合全体との一致や、OMR 0の拒否を含む
  parser出力からの一般的な合法性証明までは未接続。
  あわせて`Nat < bound`と、各要素がその範囲内にある`Option Nat`の有限性をbound一般で証明した。
  後者は行列row、L1BM addressなどのoptionalな数値fieldをまとめる部品として使う。
  `ParsedL1bSet`についても、8個のL1Bを表すbitmapが`< 256`、immodeが`< 8`の有限carrierを証明した。
  全選択は`0xff`であり、assemble3は`@0/7`を含む全64組のaddress/immodeを受理し、各入力値8を拒否する。
  `Issue.lean`にcanonical decimalの`<l1badr>[/<immode>]` parserとManualのbracketed list parserを加え、
  bitmap生成関数と、出力が有限envelopeに入る定理およびall/singleton/whitespace/invalid-entryのfixtureを置いた。
  L2BM opcode parserを`ParsedL2Op`の全variantへ接続した。既定all-set、分配/収集の向き、`fromL1b`のRust parser上の
  u8範囲、RRN reduce/reduce2、`dars`/`darw`をfixture化し、selectorを無視するRust parser branchも記録した。
  `fullSelectorMask_inFiniteEnvelope`も回帰定理として残す。
  PE式全体のparserとRust parser出力との全形式の対応はまだない。
  wait tagについては、受理範囲`1..255`とoptionalな同範囲の有限carrierを証明した。
  opcode wait tagと`ParsedLine`/正規化後の`nop`に付くoptional wait tagは`Fin 256`で
  0..255に構造上制限した。0を除く条件は有限envelopeに残している。Lean parser出力が
  assemblerの受理範囲`1..255`を満たすことの接続証明はまだない。`parseParsedWaitTag?`は
  Rustと同じhex-u8のtag tokenを`Fin 256`へ変換し、`i00`は構文として保持しつつ、
  `i100`を拒否する。top-line checkerは`i00`と`nop/0; wait i01`を拒否し、`nop/0`を
  受理する。assemble3境界証拠と合うが、これはopcode/PE/nop行全体のparserではなく、
  `parseParsedNopLine?`は単一の`nop[/count]`と単一の`wait i<hex>`を構造化する部分parserである。
  その出力をcheckerが受理した場合のtag条件はsoundness theoremから従うが、複数waitや
  modifierを含むRust `parse_line`全体、およびassemblerとの完全な対応証明はまだない。
  L1BMの`mabdiff`はassemble3でDistrib/Gather両方向について明示符号付きの`-255..255`全件を受理し、
  境界の`±256`を両方向で拒否することを確認し、
  `-256 ≤ mabdiff < 256`の部分型が有限であることを証明した。SDMの有用範囲は`0..15`。
  Leanの`parsedMabdiff?`は値をこの範囲付きsubtypeで返し、L1 opcode parserはその値からのみDistrib/Gatherを構成する。
  境界監査でRust側の`i8` parserが受理範囲を狭めていたため、`i16`保持と`[-255,255]`検査へ修正し、
  同じ境界を回帰確認した。LeanにRust `parse_l1_opcode`の全variantを構造化`ParsedL1Op`へ写すopcode parserを加え、
  broadcast/write、符号付きMAB差分、direction依存、round付きRRN reductionをfixture化した。
  Rustと同じく最初のtyped operandから`l1bmd`/`l2bmd`の方向を決める薄い入口も加えた。
  selector parserが保持するu8全域とassemble3で有効な0..15は別の範囲として扱う。
  `ParsedRrn.precision`自体を`Char`の`<128`部分型に変更し、ASCII precisionの範囲を構造で保持する。
  RRN parserはこの部分型の値しか生成できず、そこから8個のRRN opcodeの有限carrierへ写す。
  `ParsedL1Op.distrib/gather`からoffset付きvariantだけを取り出す射影を定義し、その結果が有限なtagged carrierに
  入ることを証明した。これも他の`ParsedL1Op` variantや完全なPE行の有限性は含まない。
  `l1bmm@`と`l1bmm4@`のselector 0..15をassemble3で全件確認し、両形式の16が拒否されることも確認した。
  `ParsedL1Selector.inFiniteEnvelope_finite`は`mwrite`/`m4write`のselectorだけを有限carrier化し、
  `ParsedL1Op.selectorView?_bounded`は該当operationから有限範囲への射影を示す。
  これは`ParsedL1Op`全体の有限性やparser出力に対する一般的健全性を証明しない。
  `ParsedL2Op.fromL1b`のselectorも0..7の全件受理・8拒否を根拠に有限carrier化し、
  `ParsedL2Op.fromL1View?_bounded`で範囲条件からcarrierへの射影を示した。
  これは`ParsedL2Op`全体の有限性やparser出力への一般的健全性を証明しない。
  `ParsedL1Op.inFiniteEnvelope_finite`では、全9 variantをselector、RRN precision、MAB差分の
  envelopeでタグ付き有限型へ写し、`ParsedL1Op`全体のbounded subtypeが有限であることを証明した。
  このenvelopeがassembler受理parser出力を全て含む証明、およびPE行・machineへの合成は未実装。
  `ParsedL2Op.inFiniteEnvelope_finite`も、全10 variantについてL1B set、from-L1B selector、
  RRN payloadを含むbounded subtypeの有限性を証明した。assembler受理集合との包含証明と
  PE行・machineへの合成は引き続き未実装。
  `ParsedOp.alu`のmantissa length引数をparserの型に合わせて`Option (Fin 256)`で表し、
  u8全域の走査で`hbfe`/`hbfn`は`6..9`だけ受理される観測をもとに、optional payloadの
  `[6,10)` envelopeが有限carrierであることを証明した。Lean parser自体がopcodeを解析して
  このenvelopeを保証する証明はまだない。
  これらのpayload定理から`ParsedOp`/`ParsedLine`全体への合成、他の残存Nat/Int範囲、
  パーサー出力のenvelope健全性はまだ未完了。
  operand envelopeはregion width 1/2/4/address `< 4096`/madpe `< 4`、BAR width 1または2、mask selector `< 32`、
  OMR entry `1 ≤ entry < 16`、matrix width 1/2/4/row `< 16`、L1BM width 1/2/4/address `< 8192`、
  L2BM address `< 32768`/selector `< 8`、DAR address `< 1024`を含む。
  `PEParser.lean`にforward/fixed、OMR/BAR、matrix、L1BM/L2BM、DAR、nowrite、通常の`$m/$n/$r/$s/$t`メモリoperandを構造化parserとして追加した。
  Rust parser上のu8/u32範囲、flat/連続cycle address、LM0 t-indirect、madpe、e/r suffixを扱うが、
  PE式全体やassembler受理集合との対応は主張しない。
  これは境界プローブに基づく有限な上位集合であり、bank/opcode別alignmentや、全assembler-accepted
  operandがenvelopeに入ることの証明ではない。bounded operand carrierは有限だが、これを合法PE行や
  `MNCore.machine`の全行有限性へ接続する作業は未完了。
  BAR幅は`mb`/`lmb`を受理し`llmb`を拒否する既存assemble3 probeから1または2語に制限した。
- `InstructionLine.inFiniteEnvelope_finite`: PE行の式数を10以下、nop countを任意のbound未満とし、
  wait tagと各正規化式を既存envelope内に制限したline carrierの有限性を証明した。
  MV転送sizeのenvelopeを`< 32768`とした。SDM 3.5.8.2〜.25の全MV文法について、
  size 32704を受理し32768を拒否するassemble3 probeを記録している。これは上限の観測であり、
  32768未満の全sizeが合法であることや、合法sizeが64の倍数であることは示さない。
  Rust parserからassemblerへの対応証明も未実装である。MVのアドレスなど残りのフィールドは有限な広い型のままである。現状は有限上位集合の証明であり、
  全合法lineが各payload envelopeに入ることや、固定costからnop count boundを得る証明は未接続。
- `InstructionLine.localIssueLegal`を既存のtop-line checkerへ接続し、bound付きfinite envelope内で
  PE同時発行checkerを通るline subtypeも有限であることを示した。これは局所issue条件だけであり、
  parserからの包含、MV/operandのassembler対応、行をまたぐhazardを含むprogram legalityは未接続。
- `ParsedExpr.inFiniteEnvelope`から正規化式のenvelopeへの写像を証明した。opcode固有source arityから
  source長3以下を導ける一方、opcode・operand・flushの数値範囲とdestinationの重複なしを、実parser出力に
  対して証明することは引き続きparser/assembler対応の未解決義務である。
- `evidence/output-roles/reference.json`にassemble3の84件のoperand-role probeを記録した。zero、ALU、
  MAU、matrix、L1BM、L2BMで代表的な入力/出力位置と重複出力を照合している。opcodeごとの全構文や
  Lean issue checkerとの対応証明ではなく、実parser出力がfinite envelopeのdestination-list条件を満たす
  ことも引き続き未証明である。
- 有限envelopeに`destinationsAvoidKnownSourceOnly`を追加し、source-onlyのfixed identifierとforwarding
  operandをdestination列から除外した。assemble3のzero/ALU代表probeとRust operand型に沿う必要条件で、
  opcode別の十分なdestination role checkerではない。matrix/block operandや重複・値域の対応は未完了。
- `ParsedOp.destinationRoleScreen`を導入し、scalar PE出力、matrix read/write、wait/noforwardに加えて、
  L1BM/L2BMの代表opcodeをsourceとopcodeに応じたdestination roleで絞った。finite envelopeには各destinationが
  screenを通る条件を含め、正規化で維持し、bounded expression carrierの有限性に接続した。Rustのoperand roleと
  assemble3の84 probeを根拠に、転送方向、L1BM/L2BM opcodeごとのsource bank、複数destination/重複拒否、
  DARSのL2BM source・DAR outputとDARWの無operand、`$mreadf`のALU先頭source制約を示す
  代表補題・照合を追加した。DARS/DARWの同時発行規則、全opcodeの受理構文、実assembler出力とscreen/envelopeとの
  完全な対応は未完了。
- `ParsedExpr.parserSourceArityValid`を追加し、Rust `parse_expr` の通常経路を使うALU/MAU/matrix命令は
  source数がopcodeの固定入力数に一致すること、zero-input/block-memory経路はparser上限以下であることを
  構文述語に反映した。DARSはL2BM source一つとDAR destination一つ、DARWはsource/destinationなしに絞り、
  source/destination roleと形状条件をfinite envelopeへ追加した。parser上限が3以下であることを証明し、
  正規化で条件が維持されることも証明した。
  Rust実装との完全な差分照合やdestination数・範囲の対応証明は未完了。
- `InstructionLine.pe_inFiniteEnvelope_of_parsed`は、`LegalParsedLine`がissue groupから与える式数上限10と、
  式ごとのparsed payload envelope条件から、正規化PE行が有限carrierへ入ることを導く。
  残る前提は、実parser/assemblerが各式のpayload条件を満たすこと。
- `FiniteInstructionLines.lean`: `InstructionLine.costBelowEnvelope_finite`でcostがbound未満の
  envelope付きline carrierを有限とし、`legalCostBelowEnvelope_finite`で合法line全てがそのenvelopeへ
  入る条件付き有限性を証明した。さらにMathlib `Fintype`からboundごとの
  `costBelowEnvelopeAlphabet`を構成し、包含条件のもとで合法行を覆うことを証明した。
  このalphabetは理論上の有限carrierで、列挙の計算可能性やenvelope包含は主張しない。
  さらにenvelope包含条件を満たす`legal`述語については、合法かつcost制限内の部分型に
  `Fintype`を与え、正確な`legalCostBelowFinset`/`legalCostBelowAlphabet`を構成できる。
  Finset の方は`finiteAlphabetCertificate`へ直接渡せる。合法なMN-Core行がenvelopeに入る
  一般証明と、完成したMN-Core machineへの接続はまだない。
- `InstructionLine.localIssueLegal`: parsed issue checkerと、当該行コスト+1のpayload envelopeを
  組み合わせた局所述語を定義した。コストがbound未満ならbound固有envelopeに入ることを証明し、
  `localIssueLegalCostBelowFintype`と`localIssueLegalCostBelowAlphabet`を構成した。
  alphabetの所属条件も局所合法性とコスト上限の組み合わせに一致する。これは単一行の結果であり、
  命令間hazard、parser/assembler完全性、MNCore全体のmachine合法性を証明したものではない。
- `ProgramLegality.lean`: `MNCore.partialMachine.legal`は正規化済み`InstructionLine`列を広く許す。
  発行checkerが拒否する行は`step = failure`、checkerを通る行は値遷移が未接続なので`unknown`にする。
  正規化成功後の命令列はこの広い合法性を満たす。PE/block hazardと無効なforwarding読み出しは未接続。
- 同ファイルの`boundedIssueMachine`は、以前のlocal issue・envelope・PE/block hazard条件による有限性定理を保存する
  旧projectionであり、機械の合法性や候補列挙には使わない。有限性・範囲付けの証明は凍結する。
- 候補列挙には`encodedUniverseMachine`を採用し、全426-bit PE語と82-bit MV語の有限carrierを使う。
  `InstructionLine`のbounded projectionは使わない。符号語の遷移意味論と、全assembler受理sourceからこの符号語型への
  対応は未証明なので、この選択だけで`MNCore.machine`やISA完全性が得られるわけではない。
- `scripts/check_manual_alu_inventory.py`: SDM表3.9のALU opcode集合をコンパイラ定義と比較し、精度・符号指定を
  展開した136綴りがparser監査候補に含まれることを検査する。現状はALU opcode表だけの棚卸しであり、
  全命令形式・全operand形・assembler受理の完全性証明ではない。
- B3の境界: 本プロジェクトではPE行の同時発行違反、PE/block hazard、無効なforwarding読み出し
  （例: MAU disabled）をすべて`step`の実行失敗として扱う。assemblerの`Instruction field conflict`は
  source normalization／assembly段階の失敗として別に扱う。既存のIssue・hazard checkerはstep失敗条件の証明に再利用し、
  `legal`を狭める根拠にはしない。
- `FiniteExample.lean`: 3命令・4入力の小さな機械で、全候補の反証、2行の最適性、
  限定入力では1行解が存在することを証明する回帰例。**MN-Coreではない。**
- `PlusOne.lean`: Welcome（`challenge/1.plus-one`）の2行の `iinc` 解について、
  指定範囲内の任意の16語入力で出力の自然数値が各語+1になること、0行と1行では不足することを Lean で証明。
  2行の自動ストライドが既存のPEメモリアドレス計算で各4サイクルの8語を指すことも証明。
  既存の整数ALUの64ビットバス評価が、上下2つの32ビット値を独立に1増やすことを証明し、
  `step` の書き込み値をそのバス出力から取り出すようにした。
  各サイクルのLM0長語読み出しがこの2語を供給し、ALU出力が両語の書き込み値に
  一致することも証明した。読み出しは既存のPEメモリ部品を使用している。
  `step` の LM1 書き込み値が各サイクルの ALU 出力の上位・下位語そのものになることも
  接続した。
  **命令行はこの2種類だけの限定モデル**で、他の合法命令・同時発行・制御文を
  排除していない。したがって全ISAの最適性証明には数えない。
  問題仕様の全domain（16語すべて`0..50`）に加えて、公式testcase.vsmの16入力値を固定した
  testcase-only Problemも作り、2行解の限定モデル上の正しさを証明した。testcaseの出力は
  `n0c0b0m0p0`だけを読むため、このファイルのWordsはそのPE一つをモデル化する。
  Rust `machine.rs`の`Words::get`が未割当PE SRAMをzeroで返す証拠を、初期LM1=0の選択に用いた。
  `scripts/check_welcome_reference.py`は公式testcaseの入力と期待値を使い、公式assembler/emulatorで
  2行解を実行して16出力語すべて一致することを確認する。これはtestcaseの実験照合であり、証明ではない。
  次の証明義務は、実際のVSM 2行がこの状態遷移を実現すること、
  全合法な1行命令（他の演算器・転送・同時発行を含む）では16語の+1を実現できないこと、
  ゼロコスト制御文を含む全ソースをスコア付き行へ意味保存で正規化できること。
- `IntegerALU.lean`: MN-Core整数ALUの部分的なデータパス。
  16・32・64ビットのinc/dec/add/sub/not/lnot/and/or/xor/max/min/passa、
  lsl/lsr/bsl/bsr（符号なしlsrを含む）、packbit、
  レーンの分割・結合、4ビットのフラグ複製、下位長語の素通りを実装。
  入力は読み出し・精度縮減済みのバスであり、オペランド読み出しや精度縮減そのもの、
  マスク適用、ハザード、同時発行は未実装。未対応要求は実行失敗ではなく`unknown`を返す。
- `OperatorAbstraction.lean`: すべての演算器が共有する定数・入力依存のsymbolic expression。
  定数入力だけのunary/binary/ternary演算は演算関数を正確に評価し、それ以外は入力式を保持する。
  依存に含まれる入力だけを一致させた2環境では出力が一致する、非干渉性の健全性を証明した。
  UnitKindは整数ALU、浮動小数点MAU、行列ユニット、L1BM/L2BM、MV転送、PE間転送を列挙する。
  これは全命令の接続完了を意味せず、今後は各パーサ済み命令と各state locationをこの抽象へ接続する。
- `SingleFMA.lean`: MN-Core単精度ベクトルFMAのbit-level実装。
  `vfma`と同じ省略部分積の補正定数、cの格子合わせとsticky、1回のRNE、flush-to-zero/infを整数演算で実装。
  `decide`でSDMの識別例と境界ケースを検証し、汎用定数・依存抽象のfloating MAU演算としても公開する。
  `scripts/check_single_fma_kernel.py`はRustモデルから決定的入力を生成し、Lean `by decide`で結果ビットを照合する。
  公式`gpfn3_package_main`との差分を合わせて実行するコマンドは
  `python3 scripts/check_single_fma_kernel.py --vectors 128 --seed 1234 --gpfn-runs 35`。
  Lean/Rustの全域同値証明ではない。
- `ConvertEndian.lean`: Convert Endian公開解答のALU/MAU横断変換を抽象式へ接続した。
  公式3行解では`ibsl`が32-bit各lane内の16-bit halvesを交換し、単精度FMAが定数shift laneを生成し、
  `sbsl`が各16-bit laneをbyte rotateし、`[1,0,3,2]` destination selectorが32-bit群を交換する。
  合成関数が全64-bit入力で`byteSwap64`と一致し、入力依存が抽象のdependency集合だけに限られることを証明した。
  `scripts/check_convert_endian_reference.py`は公式judge上の正解確認とRust simulator対gpfn3差分を行う。
  現在のseed 0xC0FFEEでは8値すべて一致する。命令のメモリアドレス解決・正規化・実状態遷移との対応は未証明。
- `UntypedALU.lean`: zero、imm/immuの2長語出力と、4 PE間のmsl/msrの部分モデル。
  循環転送の下位長語について、マニュアルの一般則を適用する`manualReading`と
  公式バイナリで観測した`referenceBinary`を明示的に分けている。
  未解決の差分があるため、ターゲットを指定しない循環転送は`unknown`となる。
  左右の転送で全バスが元に戻る定理は`manualReading`の場合の数学的性質であり、
  実際の循環転送命令の正しさを主張しない。
- `PEMemory.lean`: LM0/LM1/GRF0/GRF1/Tの32ビット語メモリと、アドレス計算、
  幅に応じた読み出し・ゼロ埋め、マスクなし書き込み。
  BAR/T間接値/MADPEのオフセット計算、アラインメント切り下げ、折り返しを定義。
  書き込み範囲外の値の保存と、書き込んだ語の読み戻しを証明した。
  書き込みは即時反映する組み合わせ的な部品であり、実際の命令の遅延、同時発行、
  全サイクルの読み取り後に書き込むスケジュールの正しさは証明していない。
- `MaskedPEMemory.lean`: PEメモリ宛先の単語選択と半語マージを含むmasked storeを定義。
  全選択時の既存無マスク書き込みとの一致、読み戻し、書き込み範囲外の保持を証明した。
  ParsedExpr実行器に宛先マスク書き込みを接続し、整数ALUのsource read・評価成功から
  post-flushバスを使ったmasked write後のword readbackまでを証明した。命令スケジュール、
  hazard/port legalityは未接続。
- `BusLayout.lean`: MSB側から並ぶ4本の32ビットメモリ語と、64ビット2本のALUバスを接続し、
  バスを語列へ分解して再構成すると元のバスに戻ることを証明。
  命令の読み出し・書き込みスケジュールは扱わない。
- `ParsedIntegerStep.lean`: LM0/LM1/GRF0/GRF1/Tの5バンクを持つレジスタ状態で、Tはアクセス幅に関係なく1 cycleあたり4語を読むRust挙動も証明し、
  2つの直接メモリアクセス、ParsedOpの整数ALU評価、宛先書き込みを合成し、
  対応requestの結果が宛先から読み戻せることを証明。アクセス記述子は手で与えるため、
  VSMオペランドのデコード、マスク・精度変換・遅延・ハザード・同時発行を含まず、
  全命令ステップではない。別途、cycleごとのregion、BAR、T間接語、MADPEから
  直接アクセス記述子を作る部分loweringを定義し、loweringに成功したParsedExprについて
  整数requestの存在証拠をlowering結果に保持し、その証拠だけから宛先読み戻しを導いた。
  Welcomeのplus-one ParsedExprがLM0→LM1の
  longアクセスへloweringされ、そのALU出力が既存の2語iincモデルと一致することも証明した。
  OMR宛先についても、1〜15番のlowering、ALUフラグの4ビット順序、サイクル別マスク状態更新を接続した。
  OMR書き込みは明示的なpattern/IMR選択をマスクレジスタ状態から解決し、選択後のフラグを読み戻す。
  単一行マスクが同じ命令行のmultiline directiveを取り消す優先順位も証明した。
  さらにPE行（複数式を含む）とmask directive行からなるtop-level subsetを部分loweringし、
  directiveの置換状態を既存ControlNormalizationに接続した。directive更新は選択状態だけを
  置き換えてPE/cycle/BAR/Tの実行コンテキストと累積issue語数を保持する。issueごとに時計が
  1語＝4cycle進み、directiveは時計を進めない。source全体の経過語数がnormalized issue costと
  一致する定理を追加した。複数式行は全式の入力とALU出力を
  同一の旧状態から先に準備し、その後で宛先書き込みを反映する。行全体のsingle-line mask有無も
  すべての宛先loweringへ渡す。ALU/zero/immediate line遷移にPE issue checkerを先に適用する
  入口を追加し、checkerが拒否したlineはunknownとして保留する。checkerの受理範囲自体は
  Rust parser／assembler全体の合法性との同値を意味しない。Issueモデルの合法性、source executionとnormalized issue
  executionの一致、directiveのissue costが0であること、lowering成功時の実行一致を証明した。
  nop行は指定count分のno-op issueへ展開し、register状態を保持することとscoreがcountに
  一致することを証明した。PE/nop/mask directive各行について、lowering後のissue costが
  Rustのline.words()（1/count/0）に一致する定理も追加した。これはhazard analyzerの累積step時計
  と接続する基礎である。PE行内のwait式もmachine.step同様にskipしてregister状態を保つ。
  noforward markerから既存Forwarding状態遷移への抑制信号を接続し、当該行にnoforwardがあると
  forwarding slotsが保持されることも証明した。ただし現在のParsedMaskedNormalizedMachineは
  PEメモリ状態のみを持ち、producer値・poison・wait距離・hazard状態との統合は未完了。
  nopに付くwaitタグも未モデル化。
  さらにDirectMemoryAccessイベントに対するRust hazard.rs §3.6.3.9の距離条件を形式化した。
  同一bankのLM write→PE readには3 issue word、GRF/Tの重複rangeには7 cycleを要求し、
  各境界以上で条件を満たす定理を追加した。Tのhazard address範囲はcycle番号・長さ1で扱う。
  さらに対応するParsedOperand/ParsedExpr/PE issue lineからread/write event列を生成し、
  T indirect readのcycle別Tイベントも追加する。固定patternはRust `written_cycles`と同じcycle
  bitでwrite eventを除外し、entry maskは同解析器と同じく全cycleを候補にする。
  sourceをcompileAdvancingし、directive・nopを反映したissueごとのevent列から、
  先行writeと後続readのconstraintを4 issue-word以内で集約する関数も追加した。
  生成constraintの距離・required値が上記ルールから作られることを証明した。
  さらにwrite/readイベント一覧間のconstraint出力membershipを展開し、各候補ペアの
  constraint生成と4-word window filterに対応することを証明した。
  さらにRust `Constraint::violated`相当の`distance < required`でconstraint一覧をfilterし、
  violation結果のmembershipが元一覧中の違反constraintと同値であることを証明した。
  constraint単体について、違反判定とPE pair safetyの否定が同値であることも証明した。
  Rust hazard.rs §3.6.3.1–3.6.3.8については、L1BM/L2BM resourceとL1/L2/MV pathを持つ
  別のtyped rule tableを追加し、全11 path caseのkind/distance、およびdata raceだけが
  overlapを要求しport conflictはdisjoint addressにも適用されることを証明した。
  block accessからstep/cycle単位のconstraint生成とsource event collectorの部分統合を追加した。
  既存L1Transferの`mwrite`/`m4write` pending出力spanと`pbcast` L1BM read spanをtyped eventへ写し、
  write→readのport conflict、および3 issue-word境界での12-cycle constraint生成を証明した。
  さらにRust `l1_cycle_span`の全L1 opcode表をLeanへ移し、opcode別のspanをevent化する共通関数を追加した。
  HazardTrace.leanでL1 `ParsedExpr`のsource/destinationから方向・base・width・拡張/丸め情報を読み、
  8 bank×4 cycleの32 eventへloweringする関数を追加した。source文列を走査しdirectiveを0 costとして
  issue wordごとのclockも進めてevent streamを作り、event対を既存のblock hazard ruleと
  in-window条件に通して制約を集める。L2BM opcodeのread/write spanとmulticast bank maskもParsedExprから
  lowerする。MVのLean top-level型にも転送kind/size/operand情報を持たせ、L2BM MV accessを生成して
  Rust hazard.rsのu64→u32 address/size castとbank selectorを反映し、ParsedLine列のword clockに接続した。
  MV operandのPDM/DRAM/L2BM用にdecimal/hex address、group/l2b selectorを読むLean parserを追加し、
  Rust既存fixture相当の入力とu64/u8境界拒否を証明した。Rust parser全入力との等価性、
  opcode/parameterを含むMV parserからParsedMvへの変換、
  PE operand accessとの合流、
  Rust reportのsort/dedupおよび表示値の再現は未完了。
  これは対象PEメモリ規則の条件モデルであり、Rust analyzerの全Access生成、mask directiveの実効状態、
  BARによる静的range照合、reportのsort/dedupを含む出力一致証明ではない。
  mv、debug、DRAM初期化
  など他のtop-level行はlowering対象外。精度縮減、hazard/port legalityは未接続で、
  完全な命令実行意味論ではない。
  multiline directiveの対象・entry・幅をParsedLineに保持し、mask stateの置換と通常行での保持を証明した。
  issue line全体の single-line mask 集約を定義し、マスクを持つdestinationの存在と集約flagが
  trueであることの同値、およびそのflagが同じ行の別のunmasked memory destinationで
  multiline directiveを打ち消すことを証明した。OMR対象directiveから選択フラグを解決する。
  PE/nop/mask directiveからなるlowerableなParsedLine列では、ソース順にdirectiveを適用し、
  instruction clockと合計issue costが一致する定理を追加した。`maskllm 258`の解析・lowering・
  後続issueへの状態適用も接続した。Rust parser全体からこのParsedLineを生成する対応と、
  全VSM行種別を含むソース列loweringは未完了。
  整数ALUのRust入力処理に合わせ、sourceの符号反転・精度拡張属性を無視するloweringを接続して証明した。memory sourceの丸め属性はRustと同じsingle→half変換（最近接偶数、非正規数なし）を入力readへ接続し、tie-even・境界・特殊値を計算で証明し、再梱包後のhalf ALU各laneが元busの逆順4語を読む対応も証明した。Rustの`read_alu_input`が整数ALUのmemory source mask属性を無視する意味をloweringへ接続して証明し、mask付きsourceのALU lowering例を追加した。非PEメモリは引き続きlowering対象外。forward sourceのoperand loweringと、明示slotを渡す場合の既知値・poison・unknown伝播、およびALUから宛先writebackまでの直接stepも追加した。複数式PE行を同一の旧register state/旧forwarding slotsからprepareし、一括commitするstepも追加した。prepare済みの整数ALU出力をflush後busとして指定cycleの`aluf` slotへ反映し、そのslotのreadbackを証明した。さらに整数ALU・zero・immediate producerからなるissue lineについて、全式を同じ旧register state/旧forwarding slotsから4 cycle分prepareし、Rustの式順・cycle順でwriteをcommitし、cycle別`aluf`を集める遷移を定義した。matrix readはD/H/その他single-width precisionごとにRustのphysical word配置からbusを作り、ParsedExprのsource/destination lowering、flush後のPE-memory write、cycle別`mreadf`更新を4-cycle stepとして接続し、整数ALU/constantsとmatrix readが混在する部分line遷移へ統合した。D精度のstorage-to-bus/readbackと全precisionのbus layoutを証明した。matrix-writeはD精度の未修飾PE-memory/forward sourceに対する4-cycle store更新と、F精度の未修飾sourceに対する4-cycle store更新を定義し、各cycleについて、各PEでlowerしたmemory/forward operandのread結果からPE別のD値を集め、lowering成功時にdestination side/baseがcontextによらず一定である性質を証明し、PEごとのlowering/read結果だけからD精度の4 cycle分のrow更新後readbackまで示す定理を追加した。F/G精度では各PEの2つのsource wordが8-word rowの対応位置へ入り、4 cycleのlowered/read結果が4つの更新rowを作ること、後続更新後も各rowのselected wordが保持されること、および最終storeからcycle別source wordをmatrix-read busで回収できることを証明した。G精度はRust実行器でFと同じ32-bit幅・physical row配置であり、block-float値をraw bitsのまま保持する。Gの式が同じdirect-write shapeへlowerされる定理も追加した。入力の拡張・丸め・符号反転、MAU/L1BM producer、およびそれらを含むlineは未接続。
- `Issue.lean`: Rust `AluOp::inputs()` と全32 opcodeのsource数をLeanで定義し、issue mirror監査でも両表の一致を確認する。PE式の同時発行判定について、グループ重複、MAU組み合わせ、
  行列レジスタ使用、PEメモリの読み書きポート、即値とLM0、zero-flush重複を
  抽象レコード上の述語として定義し、判定と合法性の同値を証明した。
  VSMのPE演算子・精度・丸め/符号属性・L1/L2演算子・オペランド全形式を持つ構文型を
  定義し、そこからissue判定に必要な情報を射影する関数を定義した。Rust側の`issue.rs`で
  参照されるメモリ種別・4サイクルアドレス修飾・全オペランド形を保持する。
  plus-oneのLM0長語読み出し・LM1長語書き込みの合法性と、
  ソースが不一致のベクトルFMA＋行列書き込みの拒否を証明した。
  Rust VSMパーサが使うPE式と非PE行の区別に沿った型と、投影が読み書きバンク・issue群を
  保存することも定義・証明した。Rust VSMパーサの各分岐がこのLean型を生成する対応、
  `issue.rs`以外のアセンブラ合法性規則、
  ハードウェア対応は未証明。
  zero と imm/immu を既存のBus結果・mask・PEメモリ書き戻し経路へ追加した。Rust実行器の
  constant bus構成を転記し、immの4語配置、常時0のフラグ、入力バスと縮減状態への非依存性を
  証明した。direct PE-memory destinationを持つこれらの式は複数destinationへ同じbusを書けるようにし、
  source順にprepare・commitされる定理と、LM/GRFの2 destination lowering例を追加した。
  対応する整数ALU式についても、複数のdirect PE-memory destinationをsource順にlowerし、
  同じ旧stateから個々のwriteをprepareするtraversal等価性と、分割commitが順序どおり合成される定理を追加した。
  `$nowrite` は効果なしとして除外し、OMR destinationは対応するentry/cycleへALUフラグを選択マスク付きで書き込む。OMR宛てALUのmemory sourceはmask/符号反転/拡張属性を無視し、Rustと同じsingle→half丸めを評価前に適用する。
  非PE memoryやBARなど未対応destinationを含む式は依然unknownとなる。
  整数ALUのsourceにはmemoryに加えて `$l2bid`、`$l1bid`、`$mabid`、`$peid`、`$subpeid`、`$msb1` を接続した。PE座標（group/L2B/L1B/MAB/PE）から実行系と同じ値を作り、precisionに応じた128-bit反復busを定義した。linear PE indexからの座標分解と、各固定operand値がindexから直接得られる式に一致することも証明した。パーサから実行時PE座標への全体接続とRust意味論との対応は未証明。
  Rust parser／実行器との意味対応自体は未証明。浮動小数点演算、汎用operand readと精度縮減、
  4-cycle/4-PE全体の実行、forwarding、ポート・hazard統合は未接続で、対応しない命令は`unknown`のまま扱う。
  さらに、L/I/S精度の整数ALU命令とpackbitだけを既存の部分ALU意味論へ写す関数を定義した。
  浮動小数点演算、オペランド読み出し・精度縮小、マスク、タイミング、書き戻しは未接続で、
  対応しない命令は`unknown`のまま扱う。対応対象は必ずALU opcodeに写ることと、
  `iinc`の評価が整数ALU評価と一致することを証明した。
- `AddressProperties.lean`: T間接値の4096を法とする同値性がアドレス計算を保存することと、
  MADPE閾値を超えるPEではアドレスが変わらないことを証明。
- `Masks.lean`: 固定・可変マスクエントリ、半語/単語ごとの書き込み合成、ゼロフラッシュ、
  マスクレジスタへの論理積書き込み、単一行マスクによる複数行設定の取り消し。
  フラッシュが演算フラグを変えないことと、長語マスクの書き込みでは
  下位長語が常に新値になることを定義・証明。
- `Forwarding.lean`: 4種類×4サイクルのフォワーディングスロットと、nop/noforwardによる保持、
  ALU/MAUの生成がない通常ステップでの無効化、使われるまで遅延する既知の無効値を定義。
  未実装の`unknown`は既知の無効値`poison`と区別し、捨てても意味論を完成したことにはしない。
  入力は全ユニットの使用・出力が判明したステップ概要であり、未解釈命令を「生成なし」として扱わない。
  数値演算のレーンごとの異常、初期状態、全命令の符号化・遅延のモデルは未実装。
  行列転置読み出し/L1BMの生成なしケースは既定モデルで`unknown`。
  公式ターゲットの行列読み出し生成なしでのゼロ出力は`advanceReference`という別プロファイルで明示する。
  マスクレジスタは別に計算したフラグを使うため、データの無効性だけではエラーにしない。
- `EncodedForwarding.lean`: 明示的な符号化語列向けプロファイル。
  L1BMフォワーディングの保持、次の生成による更新、noforwardによる保持を定義・証明。
  全426ビット命令のデコーダや、拒否されたVSMソースの合法性を証明するものではない。
  元のVSMモデルで未解決だった5ケースを自動昇格させない。
- `L1Transfer.lean`: Rust `Blocks::l1_to_pe` の`pbcast` raw転送について、1 L1Bの
  8192-long-word bankから各cycleのMSB long wordを読み、2-long-word source時だけ
  4位置先のLSB long wordを加えるbus配置と、L1BM address wrapを定義・証明した。
  turnaround sourceのcycle内offset 0/4と、LBF forwarding slotからの読み戻しも接続した。
  `mbcast`はcycleあたり4/8-word strideとturnaroundで常に対になる2 long wordを読む規則を、
  `m4bcast`は4-MAB group index・cycle stride・source幅別のoffset規則を定義・証明した。
  Rustの`mab >> 2` group選択もLean index関数へ接続した。`distrib`の符号付きMAB差分を
  Euclidean moduloで16 MABへwrapし、addressed sourceのcycle×64 offsetへ接続した。
  PE→L1BMの`mwrite`/`m4write` pending write列も定義し、1-word/2-word時の4/8および
  16/32書込み数と、pending list末尾書込みのcommit readbackを証明した。m4writeのsourceは
  Rust同様に(mo, selected MAB, PE)で選択し、各PEのhigh/low long wordが対応offsetの
  pending write listに含まれることも証明した。さらに`mwrite`の2-word列と`m4write`の
  最終payloadを実際にfold commitした後のreadbackを証明した。turnaround stateへの同時更新、全L1B・MAB群の
  line実行、reduce、他L1転送との同時発行は未接続。`gather`については符号付きMAB差分で
  宛先を16 MAB内にwrapする関数を共有し、cycle×64 offsetのL1BM pending writesと、元MAB順の
  turnaround pending writesを定義した。両列の64要素数と各(source MAB, PE)値の対応に加え、
  両pending列をcommitした後の最終word readbackを証明した。さらに`mwrite`/`m4write`の
  4-cycle列をcycle順に連結し、1/2-word幅ごとの総書込み数と、各cycle/PEのhigh/low payloadが
  連結列に含まれることを証明した。`reduce`/`reduce4`はRRN結果を明示入力とするpending列を追加し、
  4-group・rounding・出力幅ごとの件数と先頭payloadの配置を証明した。RRN演算値の算出、
  integer RRNのwrap-add、bitwise and/or、論理 and/or、sign-magnitude max/minを追加し、
  long word内のhalf/word/long各laneを別々に縮約して再結合する意味論を定義した。
  integer `reduce`/`reduce4`では選択MAB入力の縮約結果をpending列に接続し、出力件数を証明した。
  浮動小数点RRNではround-to-nearest-evenの右シフト、有限値の指数揃えと符号付き仮数和、
  出力形式への正規化round-pack、infinity/zero規則を定義し、singleの具体例を証明した。
  native single/doubleのlane別RRN結果をMAB選択後に`reduce`/`reduce4`のpending列へ接続し、
  1/2 long-word時の件数と両方の出力結果のアドレス対応を証明した。
  half aliasでは4 half laneをsingleへ拡張し、16 MAB時の二段縮約、halfへのround-pack、
  packed outputとL1 pending列への配置を定義・証明した。native single/doubleの明示的なhalf
  output roundingもsource/destination幅に応じたlane数・packed layoutとL1 pending列へ接続した。
  reduceのL1BM pending列とturnaround pending列を同じ状態遷移でcommitする関数を定義し、
  両出力のcommit先とturnaround列の件数・結果対応、および末尾writeのreadbackを証明した。

`Machine.positiveCost` はスコアが正の行へ正規化済みであるという条件。
MN-Coreにはゼロコストの制御文があるので、その正規化の意味保存と完全性を証明するまでは
列挙定理を元のVSM全体へ適用できない。制御文や未対応命令を勝手に不合法とみなさない。

## 監査・検証

```sh
python3 proofs_lean/scripts/catalog.py           # 入力やベンチ結果を更新したとき
python3 proofs_lean/scripts/catalog.py --check
python3 proofs_lean/scripts/check.py             # clean build + kernel依存 + 証明範囲の検査
python3 -m unittest discover -s proofs_lean/tests -v
```

`check.py` は旧 `.olean` 混入を避けるためクリーンビルドする。
RustのVSM/issue列挙型とLean投影型の列挙子の対応も照合する。
この照合は型の列挙漏れを検出するが、Rustパーサの動作とLean投影の意味対応は証明しない。
旧モジュールのimport、証拠のない `optimalProven`、`sorry`、独自axiom、
`unsafe`、`native_decide`、`decide +native`、カーネル検査の回避を拒否する。
`bv_decide` は許可し、その証明が依存するLRAT証明書のaxiom
（`<宣言>._native.bv_decide.ax_*`、Leanコンパイラを信頼境界に含める）も受理する。
カーネル依存は標準の `propext`、`Quot.sound`、`Classical.choice` と
このbv_decide証明書axiomに限定して検査する。
正しさの基準は公式エミュレータであり、Leanで証明した解はVSMとして
公式judgeで実行して照合し、不一致はモデルまたはLeanのバグとして扱う。
公開定理だけでなく、プロジェクト各モジュールの全宣言を調べる。
rootからimportされない証明ファイルも拒否する。rootのGitHub Actionsに同じ検査を設定した。
この検査はISAの完全なモデル化を代替しない。

`ALUProbe.lean`はこの整数データパスから期待値を出力する実験用プログラム。
72綴り×30組の共通入力に加え、各シフト命令に48組の境界入力を与え、
公式アセンブラ・エミュレータと比較した。上位・下位64ビットと
4サイクルのマスクフラグが2881件すべて一致した。対象は1 PE、マスクなし、精度縮減なし、
GRFのスカラアクセスのみ。全入力に対する対応証明や全ISAの網羅性ではない。
シフト量は0、1、語長−1、語長、語長+1、2×語長−1、2×語長、2×語長+1を
各レーンに独立に配置し、上位ビット無視・打ち切り・循環の境界を確認した。
`evidence/integer-alu/`に入力・期待値とソース・ツールのハッシュを保存している。
再実行にはローカルの公式ツールが必要で、通常CIは保存された証拠の整合性を検査する。

```sh
python3 proofs_lean/scripts/check_alu_reference.py \
  --output proofs_lean/evidence/integer-alu/reference.json
python3 proofs_lean/scripts/catalog.py
```

`UntypedProbe.lean`の公式比較は96命令×4 PE＝384観測で実施した。
即値はゼロ・最大値・符号境界など24種類、循環転送はPEごとに異なる入力を16組使用。
出力とマスクは事前に非ゼロで埋め、未書き込みを成功と誤認しないようにした。
最初の`manualReading`では循環転送の128観測で下位長語が不一致となった。
当時のコードと反例は`evidence/untyped-alu/initial-manual-assumption/`に保存した。
`referenceBinary`を指定したモデルは384観測すべて一致したが、マニュアルとの対応は未解決。
`coverage.json`にも未解決の差分として記録し、証明数を増やす根拠にはしない。

```sh
python3 proofs_lean/scripts/check_untyped_reference.py \
  --output proofs_lean/evidence/untyped-alu/reference.json
python3 proofs_lean/scripts/catalog.py
```

`MemoryProbe.lean`の比較はLM0/LM1/GRF0/GRF1/Tを対象に、51命令・204サイクルで
上位・下位長語の一致を確認した。単語・長語・2長語アクセス、連続ストライド、
終端からの折り返し、flatアドレス、Tの幅指定無視を含む。
対象は1 PE、BAR=0、マスク・T間接・MADPEなし。動的アドレス修飾や
一般の書き込み先・遅延を含む全命令の対応証明とは別である。

```sh
python3 proofs_lean/scripts/check_memory_reference.py \
  --output proofs_lean/evidence/pe-memory/reference.json
python3 proofs_lean/scripts/catalog.py
```

`DynamicAddressProbe.lean`は動的アドレスを別に検証する。
LM0/LM1のBARとMADPE、LM0のT間接を、120命令×4 PE×4サイクル＝1920観測で比較し、
上位・下位長語がすべて一致した。BARは0、1、2、3、4093、4095を含み、
T値には64ビット最大値や上位32ビットが非ゼロの値を使用。
MADPEは全閾値0〜3、T間接はauto/flat両方のアドレス指定を含む。
入力Tの下位長語は非ゼロにして、上位長語だけが参照されることも確認した。
マスク、ポート制約、ハザードの対応証明は含まない。

```sh
python3 proofs_lean/scripts/check_dynamic_address_reference.py \
  --output proofs_lean/evidence/dynamic-address/reference.json
python3 proofs_lean/scripts/catalog.py
```

`MaskProbe.lean`は長語・2長語マスクについて、書き込み、フラッシュ、両方、
マスクレジスタ、複数行指定、単一行による取り消しの6モードを比較する。
各サイクルで16種類すべてのフラグを通し、192命令・768観測で値とフラグが一致した。
対象は1 PEの2長語GRF書き込み。BAR/T/LMや他演算器、狭い書き込み、毒値の伝播は未検証。

この実験で既存Rustシミュレータの誤りを発見した。長語マスクが全ゼロの場合も
下位長語は書き込まれるが、以前の実装は旧値を保持していた。非ゼロの旧値と新値により
12件の不一致を再現し、Leanモデル、`viz/core/src/machine.rs`、数値仕様メモを修正した。
当時の誤った`referenceBinary`というラベルと「measured」というコメントは撤回し、
`evidence/masks/initial-simulator-assumption/`にコードと失敗記録を保存した。
これはマニュアルと公式バイナリの差ではなく、ローカルモデルの誤りだった。
Rust回帰テストも768観測すべてを再生する。有限一致は全ISAの対応証明とは区別する。

```sh
python3 proofs_lean/scripts/check_mask_reference.py \
  --output proofs_lean/evidence/masks/reference.json
python3 proofs_lean/scripts/catalog.py
cargo test --manifest-path viz/core/Cargo.toml --test mask_reference
```

`ForwardingProbe.lean`と`check_forwarding_reference.py`は、ALU/MAU/行列転置読み出し/L1BM転送の
フォワーディングについて、値の保持と無効化、書き込み抑止、捨てた無効値の次ステップでの使用を比較する。
ALUでは長語マスク、ゼロフラッシュ、マスクレジスタ書き込みのエラーも区別する。
合計42ケースの各命令列を保存し、アセンブル成功、正常値、認識できたフォワーディング実行時エラー、
それ以外の異常終了、タイムアウトを別に記録する。
アセンブラの拒否やタイムアウトを実行時エラーの反例として扱わない。
前に生成命令のないフォワーディング読み出しは、公式アセンブラの型推論で拒否される場合があるため、
この比較では一度値を生成してからユニットを無効化する。初期状態や全符号化の対応証明ではない。
最初の一律の無効化・エラー伝播モデルは39ケース中31一致・8不一致となり、
`evidence/forwarding/initial-uniform-assumption/`に凍結した。
マスクレジスタへのデータエラー伝播はローカルモデルの誤りとして修正。
行列読み出し生成なしでのゼロ出力は一般的なマニュアル対応が未解決で、L1BMの生成なし5ケースも未解決のまま保存する。
「エラーにならないから古い値を保持する」という中間の仮説も誤りで、
`matrix-retention-assumption/`に40ケース中2件の値の不一致を保存した。
通常のALUゼロ・即値命令とMAU命令の3種類で、生成なしの行列読み出し値がゼロになることを確認した。
未知ケースを成功数に含めず、アセンブラの拒否を実行時の反証に流用しない。
現在は37ケースが値・エラーとも一致し、L1BMの5ケースは未解決。
Rust回帰テストは判定可能な37ケースを再生し、未解決5ケースを成功数から除外したまま検査する。

```sh
python3 proofs_lean/scripts/check_forwarding_reference.py \
  --output proofs_lean/evidence/forwarding/reference.json
python3 proofs_lean/scripts/catalog.py
```

`LBFEncodedProbe.lean`と`check_lbf_encoded_reference.py`では、受理されたテンプレートと
独立した命令断片から、426ビットの命令語を変更せずに挿入した語列を実行する。
完全なVSMをアセンブルした際の出力（拒否の場合は途中までの出力）とも、命令語の一致を確認する。
通常ALU/MAU、複数ステップ、nop、新しいL1BM転送、noforward付きL1BM転送を含む11ケースが一致した。
通常ステップでは以前のL1BM値を保持し、新しい転送では更新する。noforwardでは更新しない。
ローカルシミュレータが生成なしでLBFを一律に無効化していた点を修正した。

11ソースのうち8件はVSM全体としては拒否される。これはエミュレータでの語列実行の証拠であり、
それらのVSM合法性や、一般的な符号化・デコード対応の証明ではない。
元の5ケースの実行時挙動を調べる情報は得られたが、VSMの証明済みケース数には加えない。
入力断片、アセンブラの出力・拒否診断、実行した語列、ハッシュを`evidence/lbf-encoded/`に保存する。
監査は命令語を変更していないことと、ソース断片・語列の挿入関係も再検査する。

```sh
python3 proofs_lean/scripts/check_lbf_encoded_reference.py \
  --output proofs_lean/evidence/lbf-encoded/reference.json
python3 proofs_lean/scripts/catalog.py
cargo test --release --manifest-path viz/core/Cargo.toml --test lbf_encoded_reference
```

`audit.json` は全73問の実行済み解の上限と形式的下限を分離する。
29・34・35番の改善解も別に公式ジャッジで再実行して保存し、実行上の改善を取り消さずに
最短性の主張だけを撤回している。証拠には入力・解・公式バイナリのハッシュを記録する。
`coverage.json` のopcode一覧はコンパイラが生成する綴りの候補に過ぎず、
ISAの網羅性・各綴りの合法性・動作の正しさを主張しない。

## 反例と信頼境界

旧 `Pkg12.lean` の「11行以下のAcceptedは存在しない」というコメントに対して、
36番の6行解が公式テストケースでAcceptedとなることを再実行で確認した。
再現・ハッシュ付き証拠の収集には `scripts/collect_evidence.py` を使う。
これは**公式テストケース上の12行下限という解釈**への反例であり、
6行解の全入力に対する正しさや、6行が最短であることを証明しない。

```sh
python3 proofs_lean/scripts/collect_evidence.py \
  --problem problems/36.matmul-trb-pkg-lm-256-16-16 \
  --solution proofs_lean/evidence/pkg36/solution.vsm --claimed-bound 12 \
  --output proofs_lean/evidence/pkg36/judge.json
```

現在のベンチ上限の信頼元は保存したジャッジ結果と公式バイナリである。
Lean上のMN-Core意味論との対応証明はまだない。
仕様、入力域、許容誤差、初期状態、命令意味論、符号化・スコア、公式バイナリとの対応を
それぞれ独立した証明義務として扱う。

基準資料は PFN の [MN-Core 2 ソフトウェア開発者マニュアル](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf)
2026-06-02版。参照PDFのSHA-256は
`2b213bddd0455eb1d1d813c10f6e5827a7d5651eb3e3452f2a08f3900e79a5a6`。
この版ではマスクフラグとL1BM折り返しレジスタの説明が改訂されている。
以前の挙動モデルとの一致を無条件には仮定しない。
