---
title: 3.6.12.14 packbit-符号部パック命令
id: 66b35ffff50d56001d00dcb6
created_unix: 1723031551
updated_unix: 1771369026
views: 33
---

# 3.6.12.14 packbit-符号部パック命令

[[packbit命令]]は第 1 入力をx、第 2 入力をyとしてx 1 とyの[[MSB]]とのビット論理和を返す。
この命令は、[[ReLU]]系命令の第 1 引数のように値の符号の情報のみがあればよい場合に、データ量を節約するために使うことができる。


```例
hpackbit $msb1 $lr0v $nowrite
hpackbit $aluf $lr8v $nowrite
hpackbit $aluf $lr16v $nowrite
hpackbit $aluf $lr24v $ls0v

```
1 半語につき 4 [[半精度]]語の[[符号ビット]]をパックする。
[[$msb1]]は左シフトにより実質的なゼロ初期値として扱うことができる。
