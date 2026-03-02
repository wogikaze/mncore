---
title: 3.6.7.10 l2bmdars/l2bmdarw-DARへの書き込み
id: 66b35ffe306631001da2455b
created_unix: 1723031550
updated_unix: 1771395992
views: 9
---

# 3.6.7.10 l2bmdars/l2bmdarw-DARへの書き込み

[[DAR]] ([[DRAMアドレスレジスタ]])は、[[DRAM間接参照]]機能のための[[DRAMアドレス]]を保持するためのメモリである。
 DARへは、[[L2BM]]から[[DARBUF]] ([[DAR書き込みバッファ]])を経由してアドレス値のコピーを行う*^5 。

DRAM間接参照用アドレス語は 32 ビット幅である。
 すなわち、L2BMから 1 長語読み出すと 2 アドレス語になる。

[[l2bmdars命令]]はL2BMからDARBUFへのコピーをサイクルあたり 128 アドレス語の速度で行う。
l2bmdarw命令はDARBUFからDARへのコピーをサイクルあたり 1 アドレス語の速度で行う。
これら 2 段階の命令でL2BMからDARにアドレス値のコピーを行う。

DARBUFはグループにつきひとつ存在し、サイズは 512 アドレス語である。
DARはグループにつきひとつ存在し、サイズは 1024 アドレス語である。

l2bmdars命令は、サイクルあたり 64 長語をL2BMから読み出し、 128 アドレス語としてDARBUFに書き込む。
 この際、長語につきMSB側 32 ビットが小さい方(偶数アドレス)、LSB側 32 ビットが大きい方(奇数アドレス)のDARBUFアドレスに対応するようにする。
L2BMからはサイクルあたり 64 長語で読み出すので、 1 ステップでちょうどDARBUF全体に書き込むことになる。
 DARBUFに対する書き込み開始アドレス指定は存在せず、l2bmdars命令を発行したステップの最初のサイクルは先頭から 128 アドレス語を書き込み、以降 128 アドレス語ずつインクリメントする。
また、l2bmdars命令の最初のサイクルでは、DARBUF読み出しアドレスの[[ゼロリセット]]と、DAR書き込み開始アドレスの指定も行う。
 l2bmdars命令を発行したのと同じステップから、l2bmdarw命令によるDARBUFからDARへの転送を開始可能である。
 l2bmdarw命令が発行されている間、DARBUF読み出しアドレスとDAR書き込みアドレスは毎サイクル 1 ずつインクリメントされる。
 いずれもアドレスが終端に到達したらラップアラウンドする。

l2bmdarwは他の任意の[[L2BM命令式]]と同時発行できる。

```l2bmdarsの文法
l2bmdars $lc<addr_c>@.<l2b_c> $dar<addr_dar>

```
```l2bmdarsの効果
MEM.darw_addr =addr_adr
MEM.darbuf_read_addr= 0
for cycle= 0:4
  forall group
    uint_t src_addr=addr_c +cycle* 64
    LongWord data[64]
    data[0:64] =MEM[group][l2b_c].l2bm[src_addr:src_addr+64]
    for i= 0:64
      uint_t dst_addr =cycle* 128 +i* 2
      MEM[group].darbuf[dst_addr] = (data[i] >> 32)
      MEM[group].darbuf[dst_addr+1] = (data[i] & ((1 << 32) - 1))

```
*^5 これはアドレス値読み出しのためにL2BMを占有する時間と、L2BMからDRAMへのアドレス値転送の帯域幅をともに節約するためである。

```l2bmdarwの文法
l2bmdarw

```
```l2bmdarwの効果
for cycle= 0:4
  forall group
    MEM[group].dar[MEM.dar_write_addr] =MEM[group].darbuf[MEM.darbuf_read_addr]
  MEM.dar_write_addr= (MEM.dar_write_addr+ 1) % 1024
  MEM.darbuf_read_addr= (MEM.darbuf_read_addr + 1) % 512

```
```例
l2bmdars $lc0@.1 $dar16;l2bmdarw
l2bmd $lc256 $lb0;l2bmdarw
l2bmd $lc512 $lb32; l2bmdarw
l2bmd $lc768 $lb64; l2bmdarw
```
[[l2bmdars命令]], [[l2bmd命令]]
1 番L2BMからDARBUFにアドレス値をコピーし、同時にDARBUFからDAR 16番地以降への書き込みを開始する。
 以降L2BMからL1BMへの分配と並行してDARへの書き込みを続ける。
