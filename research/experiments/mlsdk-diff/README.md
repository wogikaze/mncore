# MLSDK の生成プログラムで SDK 0.9 エミュレータと比べる

MN-Core SDK 0.9 の MLSDK が `emu2` 向けに生成した VSM を、同じランダムな DRAM 内容で
SDK 0.9 の公式エミュレータと Rust シミュレータに流し、VSM が宣言する DRAM 領域を全部比べる。

## 準備

SDK はホストの glibc では動かないので、公式 Dockerfile からイメージを作る。

```sh
git clone https://github.com/pfnet/mncore.git ~/dl/pfn-mncore
docker build -t mncore-sdk-minimal:0.9 \
  -f ~/dl/pfn-mncore/sdk/0.9/mncore-sdk-minimal.Dockerfile ~/dl/pfn-mncore/sdk/0.9
```

SDK の利用には MN-Core SDK の EULA への同意が必要（イメージ内 `/opt/pfn/pfcomp/licenses/`）。
`sdk_run.sh` はイメージ内の `assemble3` / `gpfn3_package_main` を `/home` をマウントして動かす
（Docker Desktop からは WSL の `/tmp` が見えないため、作業ファイルは `~/dl/tmp` に置く）。

## 使い方

```sh
./run_compile.sh ~/dl/mlsdk-work/workloads      # add, softmax, matmul, mlp_fwd, mlp_train を生成
python3 mlsdk_diff.py ~/dl/mlsdk-work/workloads/matmul.vsm --seeds 3
```

`compile_workloads.py` は MLSDK の公式サンプル（`add.py`、`train.py`）と同じ API で 5 つの関数を
コンパイルする。既定の `float_dtype` なので行列積は半精度（`hbfe`/`hmmul`/`hmfma`/`hmfmar`）になる。
VSM のヘッダの `# name: DRAM@<begin>-<end>/<Dtype>(...)` を読み、各範囲の 4 グループに型に合った
乱数を `r` レコードで入れ、最後に全範囲を `d get` で読み出す。

## 結果（2026-11-25）

| ワークロード | 比較した long word | 差 |
| --- | ---: | ---: |
| add | 49,152 × 3 | 0 |
| softmax | 32,768 × 3 | 0 |
| matmul (256×256) | 49,152 × 3 | 0 |
| mlp_fwd | 9,600 × 3 | 0 |
| mlp_train（SGD 1 ステップ） | 12,736 × 3 | 0 |

差を 0 にした修正は `../hmmul-rounding/README.md`（拡張表現の積の丸めと y の格子）。
