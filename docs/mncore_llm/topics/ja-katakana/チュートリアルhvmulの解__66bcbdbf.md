---
title: チュートリアル：hvmulの解
id: 66bcbdbfc9633c001d587f74
created_unix: 1723645378
updated_unix: 1724069457
views: 26
---

# チュートリアル：hvmulの解

がわからないので考察する
```初期値.vsm
d set $lm0n0c0b0m0p0 1 3E00428044404540     # (1, 5, 9, 13) 
d set $lm0n0c0b0m0p1 1 4000430044804580     # (2, 6, 10, 14) 
d set $lm0n0c0b0m0p2 1 4100438044C045C0     # (3, 7, 11, 15) 
d set $lm0n0c0b0m0p3 1 4200440045004600     # (4, 8, 12, 16) 

d set $ln0n0c0b0m0p0 1 3E00444046204720     # (1, 9, 17, 25) 
d set $ln0n0c0b0m0p1 1 410044C046604760     # (3, 11, 19, 27)
d set $ln0n0c0b0m0p2 1 4280454046A047A0     # (5, 13, 21, 29)
d set $ln0n0c0b0m0p3 1 438045C046E047E0     # (7, 15, 23, 31)
# $lrには0を敷き詰める
```
halfの4 * 4
安直に[[hvmul]]すると合わない
 code:hvmul.vsm
  hvmul $lm0 $ln0 $ls0
      # (1.75, 0, 4.40625, 0)
      # (2.75, 0, 5.03125, 0)
      # (3.4375, 0, 5.42188, 0)
      # (3.875, 0, 5.875, 0)
 floatに変換してみる?[[wogikaze.icon]]
 $ hvpassa $lm0 $llr0    #half→float
 code:dmp
  DEBUG-GREG0(n0c0b0m0p0,0):(1, 5) 
  DEBUG-GREG0(n0c0b0m0p0,2):(9, 13) 
  DEBUG-GREG0(n0c0b0m0p1,0):(2, 6) 
  DEBUG-GREG0(n0c0b0m0p1,2):(10, 14) 
  DEBUG-GREG0(n0c0b0m0p2,0):(3, 7) 
  DEBUG-GREG0(n0c0b0m0p2,2):(11, 15) 
  DEBUG-GREG0(n0c0b0m0p3,0):(4, 8) 
  DEBUG-GREG0(n0c0b0m0p3,2):(12, 16)
 table:n0
  p0	1,5	9,13
  p1	2,6	10,14
  p2	3,7	11,15
  p3	4,8	12,16
 これで[[fvmul]]掛けてみるか[[wogikaze.icon]]
 $ fvmul $ls0 $lr0 $lm0
  table:m0
   p0	1,45	0
   p1	6,66	0
   p2	15,91	0
   p3	28,120	0
 まま、1列目はイケてる
 $ fvmul $ls2 $lr2 $lm0
  で取れた！！
  table:m0
   p0	(153, 325)	0
   p1	(190, 378)	0
   p2	(231, 435)	0
   p3	(276, 496)	0
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):{(1, 45)  (0, 0) } #d getf $llm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p1,0):{(6, 66)  (0, 0) } #d getf $llm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p2,0):{(15, 91)  (0, 0) } #d getf $llm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p3,0):{(28, 120)  (0, 0) } #d getf $llm0n0c0b0m0 1
  
  DEBUG-LM1(n0c0b0m0p0,0):{(153, 325)  (0, 0) } #d getf $lln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p1,0):{(190, 378)  (0, 0) } #d getf $lln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p2,0):{(231, 435)  (0, 0) } #d getf $lln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p3,0):{(276, 496)  (0, 0) } #d getf $lln0n0c0b0m0 1
 p*(2)にデータを移すコマンドは無いものか...[[wogikaze.icon]]
 そもそもなんで(1,5),(9,13) * (1,9),(17,25)が(1,45),(0,0)になるのか皆目見当がつかない

table:memory
 m	r
 n	s

2024/8/19
 > [wogikaze-sub(@YSurarin)](https://twitter.com/YSurarin/status/1824400077055725865)
 > MN-Coreのアセンブリに同梱されてたTuatrialにある例題が解けない...
 > アセンブラ触ったことない人がここまで読み進められてきたのもだいぶ奇跡なんだけども
 > ヒントなり教えてほしいです
 > 
 > 解いてる途中のノート：
 > [[/mncore]] チュートリアル：hvmulの解
> [百千万億 萬（つもいよろず）(@TumoiYorozu)](https://twitter.com/TumoiYorozu/status/1825461068405285114)
> [@YSurarin](https://twitter.com/YSurarin) fvmul で、(1,5),(9,13) * (1,9),(17,25)が(1,45),(0,0) になっているのは、どのコードを実行しているのかよく分からなかったのですが、
> fvmul は 長語(f32 x2) を受け取り、長語(f32 x2) を返すので、
> fvmul $ls0 $lr0 $lm0 みたいな感じだと 1 長語しか書き込まないので、d getf すると f32 が 2 個だけで、続くもう 1 長語は 0 になります
 [[TumoiYorozu]]さんにヒントを頂けたので続き[[wogikaze.icon]]
