---
title: 3.6.7.9 l2bmi-L1BM間内部マルチキャスト
id: 66b35ffe306631001da24558
created_unix: 1723031550
updated_unix: 1771442176
views: 17
---

# 3.6.7.9 l2bmi-L1BM間内部マルチキャスト

[[L2BM]]-[[L1BM]]間のパスを利用して、L2BM内部のL1BM同士の間で 16 長語/サイクルの転送を行う。
 読み出し元も書き込み先も複数にできるので[[マルチキャスト]]と呼ばれる。

```文法
l2bmb@<l1bset> $lb<addr0> $lb<addr1>
```
@以降は[[3.6.7.1 L1B部分集合指定]]で定めた[[L1B集合]]の指定であり、これに含まれるL1Bのみから読み出しが行われる。
 [[L1B集合指定]]におけるをi、[[L1B番号]]をbとして、読み出し元とb&iが一致するL1Bに書き込みが行われる。
  ここで&は論理積である。
  例えば`<immode>`が 0 ならば、b&iは常に 0 なので、`<l1badr>`番のL1Bから読み出された値が他のすべてのL1Bに送られる。
  また、`<l1badr>`が 0 、`<immode>`が6 (=0b110)であれば、 2 進L1B番号の上 2 桁でグループ化され、0,2,4,6番のL1Bから読み出された値が、それぞれ1,3,5,7番のL1Bに送られる。
  `<immode>`は 7 にできず、L1B集合を直接指定する形式で全L1Bからなる集合を指定することもできない。
読み出しアドレスと書き込みアドレスはいずれも 16 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr0+ cycle* 16
    uint_t dst_addr=addr1+ cycle* 16
    LongWord data[16]
    for l1b_src in l1bset
      data[0:16] =MEM[group][l2b][l1b_src].l1bm[src_addr:src_addr+16]
      for l1b_dst = 0:8
        if l1b_dst& immode== l1b_src& immode
          MEM[group][l2b][l1b_dst].l1bm[dst_addr:dst_addr+16] = data[0:16]

```
```例
l2bmi@0/4 $lb0 $lb0
```
0 番L1BMから読み出した計 64 長語を1,2,3番L1BMの同じアドレスに放送し、 4 番L1BMと5,6,7番L1BMについて同じことをする。

<https://tech.preferred.jp/wp-content/uploads/2024/07/anim5.gif><https://tech.preferred.jp/wp-content/uploads/2024/07/anim6.gif>
<https://tech.preferred.jp/wp-content/uploads/2024/07/anim7.gif><https://tech.preferred.jp/wp-content/uploads/2024/07/anim8.gif>

$ l2bmi@0/0 $lb0 $lb0
 <https://gyazo.com/c470be77dafe4977f02403ab60d6c2f4>
$ l2bmi@1/0 $lb0 $lb0
 <https://gyazo.com/ca3ff9d115ea557ee8f598788c3ef050>
$ l2bmi@2/0 $lb0 $lb0
 <https://gyazo.com/cf15815034d4974543d6cbdc4cc366cd>
$ l2bmi@3/0 $lb0 $lb0
 <https://gyazo.com/2b5f71b2447c1b947bb17d90de775133>
$ l2bmi@4/0 $lb0 $lb0
 <https://gyazo.com/cdedc358be36554013e10b6a7803ae61>4
$ l2bmi@5/0 $lb0 $lb0
 <https://gyazo.com/dcd7a521dd35e3045369edf5de882bde>
$ l2bmi@6/0 $lb0 $lb0
 <https://gyazo.com/b58881b44eed33e2d7270f585cc522f4>
$ l2bmi@7/0 $lb0 $lb0
 <https://gyazo.com/d1064f00e52c9d42ba5d5d60364d1df0>
$ l2bmi@(0|1)/1 $lb0 $lb0
 <https://gyazo.com/cb692f029026b33301aa30828fd541c6>
$ l2bmi@(2|3)/1 $lb0 $lb0
 <https://gyazo.com/66003e003febc31c5fdec9fe64079d74>
$ l2bmi@(4|5)/1 $lb0 $lb0
 <https://gyazo.com/b6e147a7c5518926a1eb4ebbbc1374e5>45
$ l2bmi@(6|7)/1 $lb0 $lb0
 <https://gyazo.com/28ebfaea1a1da61c06b1debe6606a43c>
$ l2bmi@(0|2)/2 $lb0 $lb0
 <https://gyazo.com/9a144da23a6ed56e643c3e5108011271>
$ l2bmi@(1|3)/2 $lb0 $lb0
 <https://gyazo.com/f7c4675e94132a2c6a682813d3ffec23>
$ l2bmi@(4|6)/2 $lb0 $lb0
 <https://gyazo.com/e6b5c9580d145209042fdc262df1986f>
$ l2bmi@(5|7)/2 $lb0 $lb0
 <https://gyazo.com/681796c976c85771d3f0e9b4857eff58>
$ l2bmi@(0|1|2|3)/3 $lb0 $lb0
 <https://gyazo.com/56376129bb1c535066fafa00fd5f60c6>
$ l2bmi@(4|5|6|7)/3 $lb0 $lb0
 <https://gyazo.com/ceabb434aec999d4b893b49e6ee35187>
$ l2bmi@(0|4)/4 $lb0 $lb0
 <https://gyazo.com/a7af334d26366559a773b62217fb1070>
$ l2bmi@(1|5)/4 $lb0 $lb0
 <https://gyazo.com/9015361d3e6436b55147643355d3d800>
$ l2bmi@(2|6)/4 $lb0 $lb0
 <https://gyazo.com/353bbb9aec1350de37104971c5b6bd7b>
$ l2bmi@(3|7)/4 $lb0 $lb0
 <https://gyazo.com/686c7aabd359aab2d9b337f07a41ba11>
$ l2bmi@(0|1|4|5)/5 $lb0 $lb0
 <https://gyazo.com/e3a564a79782a7beeddbcfa92f4a00c3>
$ l2bmi@(2|3|6|7)/5 $lb0 $lb0
 <https://gyazo.com/302a01071d451df5170a9c95c514acef>
$ l2bmi@(0|2|4|6)/6 $lb0 $lb0
 <https://gyazo.com/a40cffad7fd0e90ffd7a4ae441af7492>
$ l2bmi@(1|3|5|7)/6 $lb0 $lb0
 <https://gyazo.com/9e440fa8df19f136d8d85260d1162de7>
