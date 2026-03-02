---
title: 3.7.1整数から浮動小数点数への変換
id: 66c8adb87a9504001dafb99d
created_unix: 1724427704
updated_unix: 1724427704
views: 5
---

# 3.7.1整数から浮動小数点数への変換

以下のアセンブリ列は 8 つの単語整数値(ここでは 100 から107)を単精度浮動小数点数値に変換する。

```txt
#Set input integers`n`for itof
imm i"100"$s0/1000
imm i"101"$s1/1000
(...omitted...)
imm i"107"$s7/1000
imm f"8388608"$lr0/1000 # 8388608is 2**23. Its weight for the LSB of mantissa is
1.0


```
```txt
ior $ls0v $aluf $nowrite# Create2**23 + 1.0 * n= 2**23 + n in float
fvadd $aluf-$lr0 $ls0v# Calculate(2 ** 23 + n) - 2**23, equals to n


```
