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
| 全短縮プログラムの列挙完全性と、候補の反証から下限を導く定理 | 汎用定理を証明済み |
| 全入力と公式テストケース限定の仕様の区別 | 定義と回帰証明を実装済み |
| 全ISAの合法な命令・オペランド・同時発行のモデル | 未実装。`coverage.json` |
| メモリ・通信・丸め・素通り・ハザード・初期化の実行意味論 | 未実装 |
| ゼロコスト制御文を含む構文と、スコア付き命令列の対応証明 | 未実装 |
| モデルと公式仕様・エミュレータの対応、信頼境界の記録 | 未完了 |
| 73問の正式な仕様とそれぞれの最適性証明 | 未実装、0/73問 |

目標全体は未完了。汎用基盤や小さな例の完成を、MN-Core全ISAの証明完成と数えない。

## 実装した定義

- `Semantics.lean`: 完全な同時発行行から状態への遷移、失敗する実行、スコア、仕様、正しさ、反証入力。
- `PartialSemantics.lean`: 未実装と既知の実行失敗を分離する。
  全命令・全状態で未実装がないことを証明しない限り、完全モデルへ変換できない。
- `Optimality.lean`: 任意の合法・正しいプログラムを量化する下限と最適性。
  証明書は全短縮候補の被覆と、それぞれの不正解の証明を要求する。
- `Enumeration.lean`: アルファベット上の任意の命令列を長さ上限まで覆う列挙定理。
  全命令・オペランド・同時発行行がアルファベットに含まれることも証明の引数に含める。
- `FiniteExample.lean`: 3命令・4入力の小さな機械で、全候補の反証、2行の最適性、
  限定入力では1行解が存在することを証明する回帰例。**MN-Coreではない。**
- `IntegerALU.lean`: MN-Core整数ALUの部分的なデータパス。
  16・32・64ビットのinc/dec/add/sub/not/lnot/and/or/xor/max/min/passa、
  lsl/lsr/bsl/bsr（符号なしlsrを含む）、packbit、
  レーンの分割・結合、4ビットのフラグ複製、下位長語の素通りを実装。
  入力は読み出し・精度縮減済みのバスであり、オペランド読み出しや精度縮減そのもの、
  マスク適用、ハザード、同時発行は未実装。未対応要求は実行失敗ではなく`unknown`を返す。
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
旧モジュールのimport、証拠のない `optimalProven`、`sorry`、独自axiom、
`unsafe`、`native_decide`、カーネル検査の回避を拒否する。
カーネル依存は標準の `propext`、`Quot.sound`、`Classical.choice` に限定して検査する。
公開定理だけでなく、プロジェクト各モジュールの全宣言を調べる。
rootからimportされない証明ファイルも拒否する。rootのGitHub Actionsに同じ検査を設定した。
この検査はISAの完全なモデル化を代替しない。

`ALUProbe.lean`はこの整数データパスから期待値を出力する実験用プログラム。
72綴り×30組の共通入力に加え、各シフト命令に48組の境界入力を与え、
公式アセンブラ・エミュレータと比較した。上位・下位64ビットと
4サイクルのマスクフラグが2880件すべて一致した。対象は1 PE、マスクなし、精度縮減なし、
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
