---
title: 3.6.1.2 c-l2bmdars命令におけるL2BM
id: 66b35ffe3c1ad7001de55f6f
created_unix: 1723031550
updated_unix: 1771369824
views: 13
---

# 3.6.1.2 c-l2bmdars命令におけるL2BM

[[l2bmdars命令]]([[3.6.7.10 l2bmdars/l2bmdarw-DARへの書き込み]])の[[入力オペランド]]にした際の[[L2BM]]は、他の[[L2BM命令]]の[[オペランド]]とは異なり次の文法を用いる。

```txt
$lc<addr>@.<l2b> 
```
[[グループ]]内のどちらの[[L2B]]のデータを[[DAR]] ([[3.6.1.3 dar-DRAMアドレスレジスタ]])に転送するかの指定のために[[L2B番号]]のフィールドが追加されている。
