# original Challenge 高級言語ベンチマーク

`*.py` は通常の Python の関数。`bindings.json` は入力の型・範囲・物理配置と許容誤差。
`kind` は説明用のタグで、コンパイラへの命令選択指定ではない。

コンパイルは `mncompile.compile_program` にソース・契約だけを渡す。
参照解やテストケースを読むのは `mncompile.challenge` の評価側だけ。
独立テストは元の入力値を変更し、別オフセット・係数・文字定数も検査する。

`generated/` は25問の生成VSM・LLVM部分IR・意味IR・条件/誤差レポートと公式テストの比較結果。
`reference-audits.json` は3つの公開最短解の反例。ユーザー指定の方針に従い、
これらを行数の達成基準から除外する。生成コードには同じ反例を回帰テストする。
未発見の反例がないことを、有限個のテストから証明したとは扱わない。

Matrix Square は追加制約「入力値は小数点以下切り捨て」を明示的な整数値制約として使う。
HSV2RGB はソースの標準 `colorsys.hsv_to_rgb` を意味プリミティブと認識する。
FizzBuzz は入力なしの純粋な定数列。ソースから全文字列を定数評価し、
型付き意味IRと分散十進レンダラを対応させる。テストケースの出力を読み出す方式ではない。

## 再現

リポジトリルートから実行する。

```sh
uv run --with numpy python -m mncompile.challenge \
  --assembler /path/assemble3 --judge /path/judge.py --output /tmp/challenge-generated

python3 -m mncompile.validation \
  --assembler /path/assemble3 --emulator /path/gpfn3_package_main --output /tmp/validation.json
```

浮動小数点の全入力誤差上界は各演算の数値モデルを前提とする。
一般的な Python 全体のコンパイル・任意配置の自動探索・VSMからの自動lifting・全機械の形式検証は対象外。
