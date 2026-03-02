---
title: 3.7.1 整数から浮動小数点数への変換
id: 6994e3b06d5991265a1f813d
created_unix: 1771365299
updated_unix: 1771365453
views: 2
---

# 3.7.1 整数から浮動小数点数への変換

以下のアセンブリ列は8つの[[単語整数値]](ここでは100から107)を[[単精度浮動小数点数値]]に変換する。
```py
# Set input integers `n` for itof
imm i"100" $s0/1000
imm i"101" $s1/1000
(...omitted...)
imm i"107" $s7/1000
imm f"8388608" $lr0/1000 # 8388608 is 2**23. Its weight for the LSB of mantissa is 1.0
ior $ls0v $aluf $nowrite # Create 2**23 + 1.0 * n = 2**23 + n in float
fvadd $aluf -$lr0 $ls0v # Calculate (2 ** 23 + n) - 2**23, equals to n


```
