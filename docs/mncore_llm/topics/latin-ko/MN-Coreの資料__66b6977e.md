---
title: MN-Coreの資料
id: 66b6977e4634f3001c110036
created_unix: 1723242369
updated_unix: 1771351150
views: 225
---

# MN-Coreの資料

[[MN-Core]]に関する資料を貯める場

https://projects.preferred.jp/mn-core/
 [[Deep Learning Processor MN Core]]
 [[公式のMN-Core紹介画像]]
 [.](https://projects.preferred.jp/mn-core/assets/MN-Core_2_whitepaper_ja.pdf)[[MN-Core 2 White Paper]]
 [.](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf)MN-Core Software Development Manual ([[MN-Core SDM]])
 [.](https://projects.preferred.jp/mn-core/assets/mncore2_emuenv_20240412.tar.xz)MN-Core Emulator Environment ([[MN-Core emuenv]])
[.](https://www.preferred.jp/ja/news/pr20240805/)賞金付きプログラミングコンテスト[[MN-Core Challenge]]を初開催 - 株式会社Preferred Networks
 [.](https://mncore-challenge.preferred.jp/)[[MN-Core Challenge]]

> [PFN Tech(@preferred_jp)](https://twitter.com/preferred_jp/status/2023680218943418867)
> 【ブログ】「MN-Core 2 Graph Compiler 自作入門」を公開しました。
> [.](https://tech.preferred.jp/ja/blog/mn-core2_graphcompiler_scratch/?=1)MN-Core2 Graph Compiler 自作入門 - Preferred Networks Tech Blog 
> 
> MN-Core Challenge にも、MNIST 実装に必要な演算を学べる教育向け問題セットを新たに追加しました。
> [.](https://mncore-challenge.preferred.jp/mnist/)Event (Additional Problems (MNIST)) 
> 
> 日頃から「コンパイラチームはどのような仕事をしているのか？」「MN-Core 上で機械学習モデルをどう動かしているのか？」といった質問を多くいただきます。今回の記事では、オープンアクセスで公開されている MN-Core 2 エミュレータを使用しつつ、小さなグラフコンパイラを動かしながら、MNIST モデルが実行されるまでの流れを詳しく解説しました。
[.](https://tech.preferred.jp/ja/blog/mn-core2_graphcompiler_scratch/?=1)[[MN-Core2 Graph Compiler 自作入門]] - Preferred Networks Tech Blog
[.](https://mncore-challenge.preferred.jp/mnist/)Event (Additional Problems (MNIST))

[[低レベル MN-Core プログラミング]]
 > 近年の深層学習をはじめとする科学技術計算では膨大な量の計算を高速に行う必要があり、GPU などの並列演算器が活躍しています。
 > これは一つ一つの計算コアは単純にする代わりに多数のコアを持つことで、トータルの計算能力を向上させるものです。
 > 深層学習の世界ではそれでもなお膨大な計算を行う必要があるため、さらにタスクに特化した設計で計算効率を改善させたアクセラレーターが多数提案されています。
 > 本講義では、そのようなアクセラレーターの一つである MN-Core に焦点を当て、そのプログラミングを行います。
 > MN-Core は深層学習での計算を念頭に厳選されたシンプルな命令セットを持ち、仕様やエミュレーターがオープンアクセスで公開されている国産アクセラレーターです。MN-Core を使用したスーパーコンピューター MN-3 は省電力性能ランキング Green500 で世界 1 位を 3 度獲得しており、Preferred Networks 社内の実ワークロードや社外向け製品でのバックエンドとしても運用されています。
 > MN-Core の低級プログラミングを通じて、CPU や GPU とは更に違うアーキテクチャを理解し、計算機の設計法やプログラミング手法としてのグラフコンパイラ（ML コンパイラ）について考える機会を提供します。

[[FOCUS講習会]]
[.](https://preferred-networks.connpass.com/event/309119/)[[MN-Core勉強会]]
 <https://www.youtube.com/watch?v=U4HjE2S8wAY>
 [.](https://speakerdeck.com/pfn/20240221-mn-core-benkyokai-updates-past-present-future)MN-Core™勉強会: [[MN-Core最新情報 - MN-Coreのこれまで、いま、これから]]
 [.](https://speakerdeck.com/pfn/20240221-mn-core-benkyokai-architecture-deep-dive?slide=60)MN-Core™勉強会: [[MN-Core Architecture Deep Dive]]

[[システム調査研究の概要と検討結果]]
 [.](https://www.r-ccs.riken.jp/assets/uploads/2025/01/events_20241227-1_research2.pdf)

[.](https://lpha-z.hatenablog.com/entry/2024/02/25/231500)MN-Core 2の機械語ゴルフに入門する - よーる
[.](https://github.com/magurofly/mncore2_test)[[magurofly]]/[[mncore2_test]]
[.](https://gist.github.com/shinh/10e2285430f07fc3c2e8b0ff397ab862)MN-Core2 vsm ゴルフ

https://x.com/PreferredNetJP
https://x.com/TumoiYorozu
https://x.com/shinh

> [not(@not_522)](https://twitter.com/not_522/status/1820416629504872807)
> コードゴルフ勢以外でも、競プロとかパズルとか並列計算とか好きな人はめっちゃ楽しめると思うのでぜひ参加してね。親切な誘導が付いているので、初心者でもゴルフ沼に直行できる親切設計です。
> [not(@not_522)](https://twitter.com/not_522/status/1820417852689785166)
> MN-Coreってアセンブリ列の行数と実行速度がだいたい比例するので、世にも珍しい「実用性のあるコードゴルフ」になってます

> [百千万億 萬（つもいよろず）(@TumoiYorozu)](https://twitter.com/TumoiYorozu/status/1820854380201169083)
> コンテストに合わせてチュートリアルも公開しますが、「待ち切れない！ Manual (SDM) を読むぜ！！」という方は、
> チップの公式ページの Emulator Environment の中に [[Tuatrial.md]]（勉強会 追加資料）があり、こちらに目を通しておくと良いと思います
<https://www.youtube.com/live/96u4dBAOzao>
 4:45:00から
