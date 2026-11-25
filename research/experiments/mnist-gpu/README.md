# GPU で MNIST train step を回す

`fx_export` が生成する `train_step` VSM を CUDA Graph で繰り返し実行し、
MNIST を 100 epoch 学習するための実験ディレクトリ。

## 結果（2026-10-20）

| 経路 | 100 epoch の test accuracy | 所要時間 |
| --- | ---: | ---: |
| VSM + GPU（この実験） | **92.29%** (9229/10000) | 24.8 分（63.7 ms/step） |
| PyTorch CPU（`haribote_graph_compiler.py train`） | 95.06% | 約 25 分 |

同じ初期重み・同じ固定バッチ順で 1 step だけ比較すると、4 つのパラメータは
PyTorch と 5e-4 以内で一致する。100 epoch で差が開くのは、VSM の行列演算が
block-float（pseudo-single）で、256 項の和で桁落ちするため。学習自体は正常。

## JIT エンジン（2026-11-25）

`gpu_train` の既定は `--engine jit` になった。プログラムを 1 つのカーネルに JIT
コンパイルし（`viz/core/src/gpu/jit.rs`）、全バッチを最初に GPU に置いて、各ステップは
バッチを DRAM へ写すカーネル 1 回と本体の起動 1 回だけにする。

| 経路 | 1 step | 100 epoch | test accuracy |
| --- | ---: | ---: | ---: |
| `--engine lines`（従来の CUDA Graph、`mnist_train_step.vsm`） | 26 ms | 約 10 分（推定） | — |
| `--engine jit` | 3.26 ms | 76 秒 | 92.27% |

30 step 後の DRAM は `lines` と `jit` でビット単位で一致する。初回だけ NVRTC の
コンパイルに数分かかり、以後は `viz/core/target/gpu-jit-cache` のキャッシュを使う。

## 直したもの

1. `viz/core` の `--replay`: capture 中に `cuCtxSynchronize` が呼ばれて落ちていた。
   capture 中だけ `sync` を no-op にした（`gpu.rs`）。
2. `fx_export/operators/gemm_impls/gemm_tra_16_256_16.py`: 行列レジスタ X4 を
   書かずに読んでいた。前段の forward が残した値が入り、fc2_weight の勾配が
   全要素 ~12,370 に飽和していた（1 step で fc2.weight が -123 になる）。
   Gemm の冒頭で X/Y をゼロクリアする。
   - 修正後、公式エミュレータ 1 step の fc2.weight は PyTorch と 2.8e-4 一致。
3. 実データを流すドライバ `viz/core/src/bin/gpu_train.rs` を追加。
   - VSM はパラメータを DRAM の同じアドレスに in-place で更新するので、
     graph を launch する前に input/target だけ upload すればよい。

## 再現

```sh
# 1. DRAM 画像と PyTorch 参照を作る（234 train batches + 39 test batches）
PYTHONPATH=. python3 research/experiments/mnist-gpu/prepare.py

# 2. 公式アセンブラを通ることを確認
judge/judge-py/mncore2_emuenv/assemble3 --instruction-mode flat \
  < research/experiments/mnist-gpu/train/train_fixed.vsm > /dev/null

# 3. 100 epoch（JIT で約 80 秒、初回はコンパイルに数分）
cargo run --release --manifest-path viz/core/Cargo.toml --bin gpu_train -- \
  research/experiments/mnist-gpu --epochs 100 \
  --program research/experiments/mnist-gpu/train/train_fixed.vsm

# 4. 評価
PYTHONPATH=. python3 research/experiments/mnist-gpu/evaluate.py \
  research/experiments/mnist-gpu/final_dram.bin
```

`prepare.py` は `init_dram.bin`, `train_inputs.bin`, `train_targets.bin`,
`epoch_orders.bin`, `reference.npz` を生成する。target は float ではなく
int32 のビット列で DRAM に置く（OneHot が整数として読むため）。
