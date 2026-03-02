---
title: 標準出入力をするためのpythonコード
id: 66b9467edf4dba001d8a8f3e
created_unix: 1723418241
updated_unix: 1723508798
views: 60
---

# 標準出入力をするためのpythonコード

前提
```py
import sys
import subprocess 

```
[[標準入力]]
 code:py
  def write_pdm(s):	# 標準入力を受け取る関数
      if not s:
          return ""
      payload = ""
      for b in s.encode():
          payload += f"{b:02x}"	# バイト列(16進数)に変換(ex. A => 41)
      while len(payload) % 16 != 0:	# payloadの長さが16の倍数になるように00を追加
          payload += "00"
      addr = f"{0:09x}"	# 000000000
      length = f"{len(payload) // 16:06x}"	# payload//16を16進数で表現
  
      vsm = f"c 0 0 i01 i00 0 {addr} {length} {payload}\n"
      vsm += "nop; wait i01\n"
      return vsm
 標準入力が`Hello`の場合
  code:hello.vsm
   c 0 0 i01 i00 0 000000000 000001 48656c6c6f000000000000000
   nop; wait i01
  [[nop]]とか[[wait]]は良いとして、[[c]]は何さ[[wogikaze.icon]]
   メモリに書けるのかい？

[[標準出力]]
 code:python
  def parse_pdm_out(out):	# 出力を変換する関数
      o = ""
      for line in out.splitlines():
          o += line.split(": ")[[1]].strip()	# 各行ごと:で区切り空白削除したものを結合
  
      s = ""
      for i in range(0, len(o), 2):	# 2文字ずつ16進数として処理
          c = int(o[[i:i+2]], 16)
          if c == 0:	# NULLなら終了
              break
          s += chr(c)
      return s

行数と出力を表示
```py
ASM = 'assemble3'
EMU = 'gpfn3_package_main'

# 標準入力からデータを読み込む
full_vsm = write_pdm(sys.stdin.read())

# コマンドライン引数で指定されたファイルの内容を追加
with open(sys.argv[1], "r") as f:
    full_vsm += f.read()

full_vsm += "f\n"
full_vsm += "e 0 0 i02 i00 0 000000000 010000\n"
full_vsm += "nop; wait i02\n"

# /tmp/full.vsmに書き込み
with open("/tmp/full.vsm", "w") as of:
    of.write(full_vsm)

# ASMコマンドの実行結果の行数を取得
score = len(
    subprocess.check_output(f"{ASM} --instruction-mode flat {sys.argv[1]}", shell=True)
    .decode()
    .splitlines()
)
print(score)
# ASMコマンドとEMUコマンドの実行
subprocess.run(
    [ASM, "--instruction-mode", "flat", "/tmp/full.vsm"],
    stdout=open("/tmp/full.asm", "w"),
)

subprocess.run([EMU], stdin=open("/tmp/full.asm"), stdout=open("/tmp/emu.out", "w"))

# /tmp/emu.outの内容を解析して出力
with open("/tmp/emu.out", "r") as f:
    print(parse_pdm_out(f.read()))
```
標準入力が`Hello`、コードが`code`の場合
 code:hello.vsm
  # write_pdm()で標準入力を変換したものを追加
  c 0 0 i01 i00 0 000000000 000001 48656c6c6f0a0000
  nop; wait i01
  
  # 元の.vsmファイル
  code
  
  # main.pyで追加
  f
  e 0 0 i02 i00 0 000000000 010000
  nop; wait i02
 → .asm → 実行 > out
 $ assemble3 --instruction-mode flat hello.vsm --output-file hello --loader
  でアセンブルすると.txtがいくつか生成された
  [[DMA]]は[[Direct Memory Access]]らしい
 code:ddma.inst.txt
  Put msi: false, ch: 0, id: 1, wd_id: 0 0000000000000000 0000000 1
  Flush
  Get msi: false, ch: 0, id: 2, wd_id: 0 0000000000000000 0000000 10000
 code:idma.inst.txt
  IDMA 28/14
  Flush
  IDMA 2/1
 [[c]]は[[Put]]
  `c <msi> <ch> <id> <wd_id> <chip_id> <addr> <payload> 48656c6c6f000000`
 　`msi`: 0ならfalse, `[[1,9]]`ならtrue
 　`ch`: `[[0,9]]`が指定できた
 　`id`: [[3.2.3 タグ]]
 　`wd_id`: タグ
 　`chip_id`: 0しか受け付けていない
 　 > chip_id must be 0 for DMA
 　多分`addr`: 16進9桁
 　 エラーに名前がない 
  `payload`: 16進8桁
   > The size of payload (8) must be 2048 bytes, which is 256 words.
　[[f]]は[[Flush]]
  [[Claude.icon]]
  > [[IDMA]]では、次の操作に進む前にすべての命令フェッチが完了していることを確認するために使用される可能性があります。
  > [[DDMA]]では、すべてのデータ転送が完了し、メモリ上で可視化されていることを確認するために使用されると考えられます。
 [[e]]は[[Get]]
 　`e <msi> <ch> <id> <wd_id> <chip_id> <addr> <dma_xfer>`
  　`msi`: 0ならfalse, `[[1,9]]`ならtrue
  　`ch`: `[[0,9]]`が指定できた
  　`id`: [[3.2.3 タグ]]
  　`wd_id`: タグ
  　`chip_id`: 0しか受け付けていない
  　 > chip_id must be 0 for DMA
  　多分`addr`: 16進9桁
  　 エラーに名前がない 
  　 > The length of this hex token must be within `[[9, 9]]` 
   `dma xfer`: データの量(words) 
    `[[1 80000]]`
    > dma xfer width must not be 0
    > dma xfer width must be less than or equal to 4MiB (512Ki words)
