---
title: 3.6.9.11 dvmul -倍精度ベクトル積演算
id: 6995652cda1b1680069d0909
created_unix: 1771398989
updated_unix: 1771399043
views: 1
---

# 3.6.9.11 dvmul -倍精度ベクトル積演算

[[dvmul]]は基本動作 [[dvfma]]の第 3 入力を 0 としたもの、すなわち[[倍精度]]で[[ベクトル積]]を計算する命令である。
 dvfma同様、`(u|d)`の指定が必要である。
```例
dvmulu $lm0v $lr0v $nowrite
dvfmad $lm0v $lr0v $mauf $ls0v
```
[[LM0]] のデータを x、[[GRF0]] のデータを yとして、
 まず dvmuluで PE0,PE1 の x*yを計算し、
 次に dvfmadでPE2,PE3 の x*yの計算をしながら[[MAU演算結果フォワーディング]]（[[3.6.1.15 mauf-MAU演算結果フォワーディング]]）を用いて PE0,PE1 の乗算結果を素通しし、
 2 命令かけて全 PE についての[[倍精度ベクトル積]] (x*y) を行い、[[GRF1]] に書き込む。
