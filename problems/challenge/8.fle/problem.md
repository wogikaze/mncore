---
source_url: https://mncore-challenge.preferred.jp/problem/fle
slug: fle
fetched_at: 2026-10-14T00:38:53+00:00
---

# Lesseq

- Top: 4 lines / syttrea
- Par: 11 lines

## Problem Statement

LM0 上の `Float` 配列 \(X\) の各要素 \(X[i]\) について、 \(X[i] \geq 1.0\) なら \(Y[i] = \infty\) （符号が \(0\) かつ指数部の全ビットが \(1\) で仮数部は任意）、そうでなければ \(Y[i] = 0\) として LM1 に出力してください。

## Explanation

様々な解法が考えられますが、MAU とマスクレジスタを使って解く方法を紹介します。
次の VSM をご覧ください。
```vsm
imm f"1.0" $nowrite
fvadd $lm0v -$aluf $omr1
imm f"inf" $ln0v/$imr1 # または imm ui"0x7f800000" $ln0v/$imr1 など
```

MAU を用いて `$lm[0:8]` から \(1.0\) を引き、ALU で `$m[i]` が \(1.0\) 以上のときにだけ `$n[i]` に \(\infty\) を書き込みます。
ここで、MAU と ALU は同時に使うことができます。
使用する入出力のレジスタが衝突していないなどの条件を満たせば、以下のように記述することで \(1\) ステップ内で同時に実行できます（3.6.4 並列実行条件）。
```vsm
fvadd $lm0v $lr0 $ln0v; isub $ls0v $t $lr8v
```

この例では MAU 命令の `fvadd` と、ALU 命令の `isub` を同時に実行しています。
しかし、以下の VSM はエラーになってしまいます。
これは「即値命令」と「LM0（`$lm8v`）へのアクセス」が同時に行えないためです。
```vsm
imm f"1.0" $lr0/1000 # /1000 は1サイクル目だけ書き込みを有効にする固定値マスクです
fvadd $lm0v -$aluf $omr1
imm f"inf" $ln0v/$imr1; fvadd $lm8v -$lr0 $omr1
imm f"inf" $ln8v/$imr1
```

即値の書き込みを工夫して、ALU と MAU を同時に利用できないでしょうか。
Tips: ALU と MAU が同時に実行可能なことや、並列実行条件に関連し、[こちら](https://mncore-challenge.preferred.jp/tips/VLIW) に MN-Core の機械語の仕組みについての説明があります。理解の補足として参考にしてください。

## Additional Constraints

* 入力 \(X\) はベクトル長 \(n=16\times4\times20\times2\) として、等差数列 `[5/n, 10/n, 15/n, ..., 5]` をシャッフルしたものが与えられます。

## Inputs

* \(X\) (\(0 \le X[{i}] \le 5\)): Float `$lm[0:40]`, `/((16_MAB:1, 4_PE:1, 20:1, 2_W:1); B@[L1B,L2B])`

## Outputs

* \(Y\): Float `$ln[0:40]`, `/((16_MAB:1, 4_PE:1, 20:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/fle/testcase.vsm)
