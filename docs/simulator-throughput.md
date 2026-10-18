# Rust シミュレータのスループット

Rust シミュレータ（`viz/core`）と公式エミュレータの実行速度を、`fx_export` の MNIST 学習 1 step で測った。
公式エミュレータを 1 コアに固定した条件で、Rust 側が約 3.9 倍速い。

## 測定結果

2026-10-19、AMD Ryzen 5 5500（6 コア 12 スレッド）、23 GiB RAM。

| バックエンド | 中央値 | 最小 | 命令語/s | PE サイクル/s |
| --- | ---: | ---: | ---: | ---: |
| Rust（`mncore-sim`） | 5.744 s | 5.689 s | 619 | 10.1 M |
| 公式エミュレータ | 22.524 s | 22.219 s | 158 | 2.6 M |
| 倍率 | **3.92x** | 3.91x | 3.92x | 3.92x |

プログラムは 3,849 行、3,558 命令語。
公式側のアセンブルは 0.139 s で、上の時間には含めていない。
Rust 側のパースも計時ループの外で 1 回だけ行う。

## 対象としたプログラム

`fx_export` の MNIST MLP（1024 → 16 → 16）の 1 学習ステップ。
forward、backward、SGD によるパラメータ更新を含み、loss は `--ignore loss` で除外した。
出力は勾配と更新後のパラメータ 9 本である。

```sh
python3 haribote_graph_compiler.py export /tmp/train_step --example train_step --ignore loss
python3 - <<'PY'
from fx_export.compile import generate_vsm_from_onnx
open('/tmp/train_step/train_step.vsm', 'w').write(
    generate_vsm_from_onnx('/tmp/train_step/mn_model.onnx'))
PY
```

生成した VSM は [viz/core/benchmarks/mnist_train_step.vsm](../viz/core/benchmarks/mnist_train_step.vsm) に置いた。
`hv*`、`hm*`、`ilrelud`、`l2bmdar*` は含まない。
したがって両バックエンドは同じ命令列を実行し、公式へのフォールバックは起きない。

## 測定方法

次のコマンドで、Rust と公式を交互に 3 回ずつ実行した。

```sh
cd viz/core
OMP_THREAD_LIMIT=1 taskset -c 2 \
  cargo run --release --bin bench_sim -- benchmarks/mnist_train_step.vsm 3 --official
```

- `taskset -c 2` で 1 コアに固定する。
- `OMP_THREAD_LIMIT=1` で公式エミュレータの OpenMP を 1 スレッドに制限する。
- Rust 側はもともと単スレッドである。
- DRAM と PDM は両方ともゼロ初期化する。実入力は使わないが、計算量は入力値に依存しない。
- 空プログラムの固定費は 3.5 ms で、5.7 s に対して無視できる。

`bench_sim` は [viz/core/src/bin/bench_sim.rs](../viz/core/src/bin/bench_sim.rs) にある。
プログラムをパースし、`Sim` を作り直して実行する時間を測る。
`--official` を付けると、公式アセンブラで 1 回アセンブルしてから、同じ回数だけ公式エミュレータを実行する。

## 注意点

公式エミュレータは既定で約 2 スレッドを使う。
スレッドを制限しない場合の実時間は 9〜21 s で、このマシンの他の負荷でも振れた。
1 コア同士の 3.92x が実装の差に近く、実時間の差は 1.6〜3.8x になる。

1 エポックは 60,000 / 256 = 235 step である。
公式が 22.5 s/step なら約 88 分、Rust が 5.7 s/step なら約 22 分になる。
この換算にはデータ転送とプロセス起動を含まない。

測定は 3 回の中央値で、マシンには他のプロセスが動いていた。
同じコマンドを再実行すれば数割は変わりうるが、倍率は 3.8〜3.9x で安定した。
