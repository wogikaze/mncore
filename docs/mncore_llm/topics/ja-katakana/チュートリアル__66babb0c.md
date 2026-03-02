---
title: チュートリアル
id: 66babb0cb2f844001c0e7d93
created_unix: 1723513615
updated_unix: 1724426461
views: 143
---

# チュートリアル

[[エミュレータ]]に同梱されていた[[Tuatrial.md]]

[[MN-Core勉強会]] 追加資料

tarballを解凍すると以下のファイルが見つかると思います。
 `mncore2_dev_manual_ja.pdf`: [[- ソフトウェア開発者マニュアル]]
 `assemble3`: アセンブラ
 `gpfn3_package_main`: エミュレータ


`./assemble3 --help`などを実行して手持ちの環境で動作することを確認したら 
 以下のコードを適当なファイル(sample.vsmとします)に書き込みます。
 code:sample.vsm
  d get $lm0n0c0b0m0p0 1
ファイルが用意出来たら次のコマンドを実行します。
 code:sh
  $ ./assemble3 sample.vsm > sample.asm

ここまで問題がなければsample.asmをエミュレータで実行してみます。
 code: (sh)
  $ ./gpfn3_package_main -i sample.asm -d dump.txt
  $ cat dump.txt
これで以下のような出力が得られたら実行環境は問題ありません。
 code:dump.txt
  DEBUG-LM0(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $lm0n0c0b0m0p0 1
 ✅[[wogikaze.icon]]

以降の文章では断りのない限り
 `d get`を含むコードブロックは実行可能な[[vsm]]([[MN-Coreアセンブリ]])であり
 それを上と同じ手順で実行して得られる[[dump.txt]]の出力を直後のコードブロックに載せています。
 vsm中の`#`以降は[[コメント]]です。

[[1 PE (1/4096 MN-Core2) での実行]]

[[1MAB=4PE (4/4096 MN-Core2)]]

[[1L1B=16MAB (64/4096 MN-Core2)]]

今回のチュートリアルはここまでです。以降に記す、より上位の階層を利用したvsmもエミュレータは実行できますが、要素数が多すぎて`d get`や`d set`による手動の検証は実用的でなくなってきます。
次回のMN-Core勉強会ではより高度な環境を提供出来たらと思います。

[[1L2B=8L1B (512/4096 MN-Core2)]]

[[Package=4Group=8L2B (4096/4096 MN-Core2)]]
