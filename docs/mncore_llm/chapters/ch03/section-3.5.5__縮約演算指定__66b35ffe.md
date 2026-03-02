---
title: 3.5.5 縮約演算指定
id: 66b35ffeb79700001c1895df
created_unix: 1723031550
updated_unix: 1723944188
views: 57
---

# 3.5.5 縮約演算指定

[[縮約転送]]では、基本モード部の`mvr`の後ろに[[演算精度]]と[[演算種別]]を指定する。
具体的な文法は以下である。
`d, f, h`が[[浮動小数点数]]の倍・単・半精度
`l, i, s`が整数の倍・単・半精度である。

```txt(py)
<rrn_opcode> ::=
| (d|f|h)fadd# floating-point add
| (d|f|h)max# max of floating-point values
| (d|f|h)min# min of floating-point values
| (l|i|s)iadd# integer add
| (l|i|s)band# bitwise logical and
| (l|i|s)and# logical and
| (l|i|s)bor# bitwise logical or
| (l|i|s)or #logical or
```
この指定は[[L2B]]以下の[[縮約命令]]においても用いられる。

[[fadd]]
[[max]]
[[min]]
[[iadd]]
[[band]]
[[and]]
[[bor]]
[[or]]
