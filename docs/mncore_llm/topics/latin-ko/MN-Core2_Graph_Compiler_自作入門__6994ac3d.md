---
title: MN-Core2 Graph Compiler 自作入門
id: 6994ac3dcebd54d30d32d8c9
created_unix: 1771351102
updated_unix: 1771355363
views: 2
---

# MN-Core2 Graph Compiler 自作入門

[.](https://tech.preferred.jp/ja/blog/mn-core2_graphcompiler_scratch/?=1)MN-Core2 Graph Compiler 自作入門 - Preferred Networks Tech Blog
[.](https://github.com/pfnet/mncore_simple_graph_compiler_for_education)[[pfnet]]/[[mncore_simple_graph_compiler_for_education]]
[.](https://mncore-challenge.preferred.jp/mnist/)Event (Additional Problems (MNIST))
[.](https://speakerdeck.com/pfn/202512_mncore-graph-compiler-mnist)[[MN-Coreグラフコンパイラを自作してMNISTを学習させよう]] - Speaker Deck

[[低レベル MN-Core プログラミング]]で扱った[[グラフコンパイラ自作入門]]の一般公開版
 MN-Core がどのように AI で使われる計算を行うのかを知る
 Python で記述された AI モデルを、グラフコンパイラがどのように処理して AI チップ向けのアセンブリを生成するのかを知る

[[Graph Compiler]]とは
 プログラムの計算手順を[[計算グラフ]]という形式で表現し、最適化するソフトウェア
  [[OpenXLA]]: [[TensorFlow]]/[[JAX]]に統合、TPU最適化向き
  TorchInductor: [[PyTorch]]の標準コンパイラ([[torch.compile]])
  Apache TVM
  ONNX Runtime
  MLIR
  [[PFVM]]
   MN-Core向けコンパイラ
 汎用コンパイラとグラフコンパイラの違い
 　汎用：命令レベルの最適化にとどまる
 　高レベルなノードとして見て、パターンを見て最適化(Fusion)する
 最適化内容
  Pythonコード
  　計算グラフのトレース：計算グラフを抽出
  ↓高レベルグラフ
  　グラフ最適化：より高速に実行できるグラフへ変換
  　演算の融合・分解、メモリレイアウトの変更
  ↓最適化済みグラフ
   ターゲットに適した高速な機械語を生成
  実行可能コード
 ことば：
  [[自動混合精度]]
  　weightや演算の精度をアーキに合わせて落とし、計算速度を上げる
　　Gemm：行列積
　　DFT：[[離散フーリエ変換]]

実際にやってみる
　用意されたもの
　　Pytorchで記述されたモデルをC++にコードに出力・コンパイル・実行する
　　(途中まで)MN-Core 2用のコードを出力する機能
 メモ
  28x28の画像
  隠れ層は1層、サイズは16
  pytorch to onnx
   $ ./haribote_graph_compiler.py export
  onnx to c++
   $ ./haribote_graph_compiler.py test /tmp/train_step
  実際にtrain
   $ ./haribote_graph_compiler.py train_cpp
  unit test
   $ make build_mn_unittest
   $ ./haribote_graph_compiler.py test unit_tests/Add_256x10_10_256x10/
 1演算ごとにVRAM→LM→VRAMにデータを流す
 　使用するDRAMアドレスのプランロジックは実装済み
 　入力サイズを784→1024に
 　出力サイズも10→16にパディング
  それぞれのopを実装すれば最低限動く
   [.](https://seccamp-2025.mncore-challenge.preferred.tech/)MNIST Op Impl for MN-Core2
   に実装があるので、Opの入出力のLocation(DRAM, LM0, LM1), address, lengthを確認して入出力を入れ替えられるようにする
   想定外の入力は無視か`raise NotImplementError`でok

 順伝播
  y = Wx + b
  活性化関数:非線形性を導入するための関数(今回は[[ReLU]])
 逆伝播
  Lossを計算
  重みとバイアスをどのように調整すべきか示す勾配(grad)を計算する
  モデルの出力と正解ラベルの差分を元に計算された勾配を起点に、微分演算に従って入力側（前の層）へと逆向きに伝播させていくことで各パラメータの勾配を求めます。
  例えば、ReLU の微分は Step 関数、行列積（Gemm）の微分は転置を使った行列積として計算されます。
 パラメータ更新
  計算された勾配に「学習率（Learning Rate）」を乗算し、現在の重みとバイアスから差し引くことで、パラメータを更新します。これにより、損失が小さくなる方向へモデルのパラメータが調整されます。
  独自アーキテクチャ用の計算コードを出力することに焦点を当てているため、モデルの自動微分パートは PyTorch の Autograd（自動微分）機能を使い、計算グラフを構築しています。
