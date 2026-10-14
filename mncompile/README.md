# 誤差予算付き MN-Core コンパイラ

通常の Python の制限された部分集合から、型・入力範囲・配置・許容絶対誤差を指定して VSM を生成する。
多項式の近似候補の探索と、配列演算用の MN-Core 専用命令選択・スケジュールを実装している。
標準ライブラリと LLVM の `opt` を使う。LLVM 18.1.3 で検証している。

## original Challenge

25問の読みやすい高級言語ソースは [benchmarks/challenge](benchmarks/challenge) にあり、
型・範囲・物理配置は [bindings.json](benchmarks/challenge/bindings.json) に分離している。
全25問で公式テスト Accepted。22問は収集した公開最短解と同じ行数で、残る3問は下表の反例があるため行数基準から除外する。
公開 Accepted と問題文の全入力で正しいことは別なので、除外は再現できた反例に限定する。

| 問題 | 生成行数 | 公開最短 | 除外した公開解の反例 |
| --- | ---: | ---: | --- |
| Plus Two | 6 | 5 | 全入力0。公開解は固定入力の並べ替えに依存 |
| Lesseq | 6 | 4 | 入力0に対して、0でなく +∞ を出す |
| Transpose / local | 16 | 10 | `X[1,0]=-0.0` で別要素の1が消える |

反例・入力VSM・期待値・実測値・対象 submission は [reference-audits.json](benchmarks/challenge/reference-audits.json) に保存している。
Plus Two の6行は、問題の公式チュートリアルの9行より短い。
全問の行数と公式テスト結果は [generated/progress.json](benchmarks/challenge/generated/progress.json) を参照。
`line_target_complete` は行数条件だけの判定。全入力の誤差評価と独立テストも別に確認する。
`formal_whole_domain_proof: false` を明記し、公式テストの成功を形式証明とは扱わない。

```sh
uv run --with numpy python -m mncompile.challenge \
  --assembler /path/to/assemble3 --judge /path/to/judge.py \
  --output /tmp/mncompile-challenge

python3 -m mncompile.reference_audits \
  --assembler /path/to/assemble3 --emulator /path/to/gpfn3_package_main \
  --output /tmp/reference-audits.json

python3 -m mncompile.validation \
  --assembler /path/to/assemble3 --emulator /path/to/gpfn3_package_main \
  --output /tmp/validation.json
```

コンパイラは問題名・参照解・テストケースを読み込まない。比較用ハーネスだけがそれらを読む。
`compile_program` はソースの演算構造から適用可能な命令選択規則を探し、行数の少ない候補を選ぶ。
bindings の `kind` は説明用で、命令選択には使わない。
Matrix Square は問題文の「小数点以下を切り捨てた入力」という追加制約を `integral_values: true` として扱う。
この制約なしに Half 行列演算を選ぶことはない。

```python
from mncompile import Tensor, compile_program

compiled = compile_program(
    "def f(x):\n    return [v + 1 for v in x]\n",
    inputs={"x": Tensor("i32", "m", 0, 16, 0, 50)},
    output=Tensor("i32", "n", 0, 16, 1, 51),
)
print(compiled.vsm)  # iinc 2行
```

単独の bindings オブジェクトをJSONに保存すれば、CLIからも使える。

```sh
python3 -m mncompile source.py --bindings contract.json --output /tmp/kernel
```

配列演算には、整数 map、比較、gather、転置、縮約、行列積、包含判定、転倒数、ビット反転、HSV→RGB、
定数列・文字列生成がある。対応する意味と配置・形状に制限があり、任意の Python をコンパイルするものではない。
複雑な演算は意味IRの専用プリミティブから、検証したネイティブ・ライブラリのスケジュールへ下げる。
公開解の命令選択の工夫を参考にした規則もあるが、入力値の埋め込みや解答ファイルの再生はしない。

LLVM 最適化後の演算グラフを読み戻すのは scalar polynomial / integer map 等の経路。
行列・縮約・文字列等では LLVM は項・インデックス・定数等を最適化し、全体の処理は意味IRと専用規則が保持する。
LLVM が単独で公開最短スケジュールを発見した、という実装ではない。

## 誤差で変わるコード

```python
def kernel(x):
    return x + 0.001 * x * x
```

リポジトリルートで実行する。

```sh
python3 -m mncompile mncompile/examples/near_identity.py \
  --domain -1 1 --atol 0.00001 --output /tmp/mncompile-tight

python3 -m mncompile mncompile/examples/near_identity.py \
  --domain -1 1 --atol 0.002 --output /tmp/mncompile-loose
```

| 入力範囲 | 許容絶対誤差 | 選択される計算 | VSM 行数 / 8 Float / PE |
| --- | --- | --- | --- |
| `[-1, 1]` | `1e-5` | 元の多項式 | 13 |
| `[-1, 1]` | `0.002` | `x` | 1 |

`--assembler /path/to/assemble3` を付けると全候補を公式アセンブラで検証し、出力された `j` と `m` の個数で比較する。
上の13行・1行は公式アセンブラで確認した値。指定しない場合は、生成 VSM の命令行数で評価し、その旨をレポートに記録する。
`--words 32` のように、PE あたりの Float 要素数を8の倍数で指定できる。

`examples/mul7.py` は定数を T に一度だけ置き、32 Float/PE を5行で処理する。
`--domain -512 512 --atol 0.001 --words 32` で生成したコードは、
既存の `problems/2.fmul7/testcase.vsm` に対して公式 judge で `ACCEPTED!! score=5` を確認済み。
ここでの `0.001` は実数多項式を参照するコンパイラの誤差予算で、問題のジャッジ許容誤差とは別の指定である。

```python
from mncompile import compile_source

compiled = compile_source(
    "def f(x):\n    return x + 0.001*x*x\n",
    domain=(-1, 1),
    atol=0.002,
)
print(compiled.vsm)
print(compiled.report["error_bound"])
```

## パイプラインと成果物

```text
Python の制限された関数
 → 意味IR / 有理数係数の多項式
 → 元の式 + 次数を変えた Horner 形式の候補
 → LLVM IR / instcombine, early-cse, dce
 → 最適化された演算グラフの読み戻し
 → 誤差解析 + GRF 割り当て + VSM スケジュール
 → 誤差予算を満たす候補の行数比較
```

上記の多項式経路では、LLVM から読み戻した演算グラフを実際に VSM 生成に使う。
共通部分式を共有し、LLVM の定数畳み込みで係数が変わった場合も、その変化を近似誤差へ加える。
`fast-math`、演算順序変更の許可、FMA contraction は使用しない。

出力ディレクトリには次を保存する。再実行時は同名の成果物を上書きする。

- `kernel.vsm`: 選択された MN-Core 2 プログラム。
- `kernel.ll`: 最適化後の LLVM IR。専用プリミティブでは項や定数等の部分IR。
- `semantic.json`: 元の式・配列演算・論理形状・選択された規則の意味IR。
- `report.json`: 入力範囲、誤差上界、前提条件、選択候補と行数等。多項式経路は全候補と LLVM バージョンも保存。

## 多項式経路の誤差の意味

参照する計算は、**入力 Float の数値を実数として代入した多項式**。
Python の float 演算を逐次実行した結果や、既存の VSM のビット列を参照するモードはまだない。
ソースの小数リテラルは Python の binary64 値を正確な有理数にして扱う。

入力の契約は、指定範囲内の有限な MN-Core Float の正規化数と0。
NaN・無限大・IEEE subnormal 入力は対象外。符号付き0の区別は実数の誤差では測らない。
入力の配置は、全 PE の LM0 先頭に `--words` 個の Float、出力は LM1 先頭。
テンソルの論理形状や PE 間の配置はこの初期実装では変更しない。

上界の計算に浮動小数点の丸めを使わず、有理数を使う。
`error_bound` の分数表記が判定に用いた値で、`error_bound_float` は表示用。

1. 多項式の差 `Σ d[k] x**k` を、`R = max(abs(low), abs(high))` として `Σ abs(d[k])*R**k` で押さえる。
2. 定数の Float 化と subnormal の0化による差を加える。
3. 各演算の誤差を、加算では `ea + eb`、乗算では `Ma*eb + Mb*ea + ea*eb` で伝播させる。
4. 演算ごとに、下記の MN-Core Float モデルの丸め・打ち切り誤差を加える。
5. 中間値のオーバーフローを除外できない候補や、上界が予算を超える候補を棄却する。

### 対象演算の数値モデル

対象は `fvmul` と `fvadd`。FMA、行列演算、半精度、精度拡張は生成しない。
`viz/core/src/float.rs` と `docs/dataflow-viz/NUMERICS.md` にある既存モデルを前提に、
演算の絶対誤差を保守的に次で押さえる。

```text
mul: 2**-22 * abs(a*b)       + 2**-126
add: 2**-22 * (abs(a)+abs(b)) + 2**-126
```

単精度 RNE の相対誤差 `2**-24` に加え、乗算の下位5ビットどうしの部分積を省く誤差と、
加算入力のアラインメントを含めた緩い係数として `2**-22` を使う。
乗算の部分積については、24ビット仮数の積に対して下位積の変更が最大でも `2**10` 未満なので、
正規化された非零の積に対する相対差は `2**-36` 未満。
加算は `a*1+b` の経路で、アラインメントの刻みが `2**(exponent(a)-41)`。
0へのフラッシュの絶対誤差として `2**-126` を加える。

これは**この数値モデルを前提にした全入力範囲の上界**であり、ハードウェア自体を形式検証した証明書ではない。
公式エミュレータとの標本比較は別途テストし、全入力の機械実装との一致証明とは区別する。
不必要に緩い上界で候補を棄却することがある。

## 多項式経路の範囲と今後の拡張

対応するソースは1引数の関数、局所代入、`+`、`-`、`*`、非負整数定数のべき乗。
多項式の次数は16以下。関数呼び出し・分岐・ループ・除算などは明示的に拒否する。
予算を満たす候補がなければコンパイルは失敗する。

最適性は**列挙した元の式と次数別 Horner 候補の中での最小**。
全 VSM プログラムの大域的な最短性は主張しない。
GRF は単純割り当てで、待機には保守的な nop を入れる。
配列経路には MN-Core 専用の命令選択・同時発行・転送規則がある。配置の自動探索や一般的なレジスタ割り当ては未実装。
Half doubling は誤差0なら13行、`atol >= 2^-30` なら9行の候補を選べる。
低精度化・FMA・縮約等はそれぞれ専用の数値モデルと前提条件をレポートに記録する。

既存 VSM の lifting と往復変換は `docs/vsm-ir.md` の別の入口として接続する。
既存 Accepted 解答は命令パターン・配置・スケジュールを評価する比較対象にする。
exp 等の非多項式の近似や、未登録の演算構造・配置を自由に組み合わせる汎用コード生成は未対応。

## テスト

```sh
python3 -m unittest discover -s mncompile -t . -v

MNCORE_ASSEMBLER=/path/to/assemble3 \
MNCORE_EMULATOR=/path/to/gpfn3_package_main \
python3 -m unittest discover -s mncompile -t . -v
```

後者は生成プログラムを公式エミュレータで実行し、境界値と固定 seed の入力について、
実際の出力誤差が報告した上界に収まることも検査する。
Half は範囲内の全30,724表現、log2・mod3・整数mul7・FizzBuzz-PE は全入力値と各レーン、
ビット反転は全1024基底、Contains は全1001キーの単独出現と重複を検査する。
さらに独立した行列、HSVのセクター境界、符号付き0、文字定数の変更、全文字出力、別オフセット等を検査する。
これは数値モデルに基づく根拠と回帰テストの組み合わせであり、全VSMの形式的な同値性証明ではない。
[validation.json](benchmarks/challenge/validation.json) に最新の件数・結果・Python実装のSHA-256を保存する。

## 参考

- [PolyBake](https://github.com/t3tra-dev/polybake): 入力領域と誤差予算を受け取り、意味IR・最適化・誤差の根拠を分ける構成を参考にした。実装コードの転載や依存追加はしていない。
- [LLVM opt](https://llvm.org/docs/CommandGuide/opt.html): 使用する最適化パスの実行方法。
- [LLVM floating-point semantics](https://llvm.org/docs/LangRef.html#fast-math-flags): 浮動小数点の変換を許可するフラグの意味。
