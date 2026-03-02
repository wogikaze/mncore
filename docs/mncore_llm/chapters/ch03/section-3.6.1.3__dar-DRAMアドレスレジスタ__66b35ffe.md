---
title: 3.6.1.3 dar-DRAMアドレスレジスタ
id: 66b35ffe3c1ad7001de55f72
created_unix: 1723031550
updated_unix: 1771369687
views: 15
---

# 3.6.1.3 dar-DRAMアドレスレジスタ

[[DAR]] ([[DRAMアドレスレジスタ]])は、[[l2bmdars命令]]([[3.6.7.10 l2bmdars/l2bmdarw-DARへの書き込み]])の出力にのみ用いられるオペランドである。
 文法は次の通りである。

```txt
$dar<addr>
```
`<addr>`はDARの書き込み開始[[エントリ番号]]である。
 [[DAR]]は[[グループ]]あたり 1 つ存在し、それぞれ 1024 [[エントリ]]である。
