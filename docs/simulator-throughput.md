# Rust シミュレータのスループット

Rust シミュレータ（`viz/core`）と公式エミュレータの実行速度を、`fx_export` の MNIST 学習 1 step で測った。
PE ローカルの高速パスと rayon による PE 並列を入れた現在のコードでは、1 スレッドで約 5.7 倍、6 スレッドで約 11 倍速い。

## 測定結果

2026-10-19、AMD Ryzen 5 5500（6 コア 12 スレッド）、23 GiB RAM。
同じ時間帯に実行した。

| バックエンド | 中央値 | 命令語/s | PE サイクル/s |
| --- | ---: | ---: | ---: |
| Rust 1 スレッド | 5.15 s | 691 | 11.3 M |
| Rust 6 スレッド | 2.77 s | 1286 | 21.1 M |
| 公式エミュレータ（1 コア） | 29.28 s | 121 | 2.0 M |
| 倍率（1 スレッド / 6 スレッド） | 5.7x / 10.6x | | |

プログラムは 3,849 行、3,558 命令語。
公式側のアセンブルは 0.14 s で、上の時間には含めていない。
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

Rust 側は [viz/core/src/bin/bench_sim.rs](../viz/core/src/bin/bench_sim.rs) で測る。
`Sim` を作り直して実行する時間を、指定した回数の中央値で出す。

```sh
cd viz/core
RAYON_NUM_THREADS=1 cargo run --release --bin bench_sim -- benchmarks/mnist_train_step.vsm 3
RAYON_NUM_THREADS=6 cargo run --release --bin bench_sim -- benchmarks/mnist_train_step.vsm 3
```

公式側は、アセンブルした命令列を 1 コアに固定して実行する。

```sh
judge/judge-py/mncore2_emuenv/assemble3 --instruction-mode flat \
  < viz/core/benchmarks/mnist_train_step.vsm > /tmp/mnist.asm
OMP_THREAD_LIMIT=1 /usr/bin/time -f '%e s' taskset -c 2 \
  judge/judge-py/mncore2_emuenv/gpfn3_package_main \
  --offchip-memory-init zero -i /tmp/mnist.asm
```

- `OMP_THREAD_LIMIT=1` で公式エミュレータの OpenMP を 1 スレッドに制限する。
- DRAM と PDM は両方ともゼロ初期化する。実入力は使わないが、計算量は入力値に依存しない。
- 空プログラムの固定費は 3.5 ms で、5 s に対して無視できる。

## 並列実行

`viz/core` の `run_fast` は PE を rayon で並列化する。
既定のワーカー数は物理コア数で、論理 CPU が 6 を超えるマシンでは論理数の半分を使う。
`RAYON_NUM_THREADS` で上書きできる。

PE ローカルの行だけが並列化の対象で、L1/L2、行列、msr を含む行は直列に残る。
6 スレッドでの高速化が 2 倍程度にとどまるのは、この直列部分とメモリ帯域のためである。

## 注意点

公式エミュレータは既定で約 2 スレッドを使う。
スレッドを制限しない場合の実時間は 9〜21 s で、このマシンの他の負荷でも振れた。

1 エポックは 60,000 / 256 = 235 step である。
公式が 29.3 s/step なら約 115 分、Rust が 6 スレッドで 2.77 s/step なら約 11 分になる。
この換算にはデータ転送とプロセス起動を含まない。

測定は中央値で、マシンには他のプロセスが動いていた。
同じコマンドを再実行すれば数割は変わりうる。
