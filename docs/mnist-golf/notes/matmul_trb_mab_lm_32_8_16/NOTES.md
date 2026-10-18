# matmul_trb_mab_lm_32_8_16 — 16 行化の試行メモ（未達）

現行全体最短は `problems/37.matmul-trb-mab-lm-32-8-16/answer.vsm` の 17 行（公式 judge ACCEPTED）。

## 確認できたこと

1. `scratch/mnist_golf/.../cand1.vsm` の 16 行構成は、T の設定を除いて**正しい**。
   T を正しく与える 2 行（`imm ui"0x00000003" $nowrite` + `llsl $mabid $aluf $t`）に差し替えると
   `ACCEPTED!! score=17`（`t17.vsm`）。つまり 16 行化に必要なのは T の 1 命令化だけ。
2. **T は 4·mabid か 8·mabid でなければならない**（全 PE で同一値）。
   - 判定は MAB 0 の LM1 のみ。C 行 0–3 は MAB 0 自身の gmmul 出力（LM1 語 0–15）で埋まり、
     行 4–31 は MAB 2g（T=4m のとき）または MAB g（T=8m のとき）の GRF0 を
     折り返し放送 `l1bmm@2g` / `l1bmm@g` で運ぶ。放送先は行あたま 4·row の固定アドレス。
   - したがって放送元 MAB の読む A 行が 4g..4g+3 でなければならず、
     行先頭 = T/2 が 4 の倍数（＝ T が 8 の倍数）または T=4m（行先頭 2m）が必要。
3. T を書く 1 命令で得られる値（実測、`probe2.py`）:
   | 命令 | T (語アドレス) | 行先頭 |
   |---|---|---|
   | `ipassa $mabid $t` | m | m/2（偶数 m のみ） |
   | `ipackbit $mabid $ls0 $t` | 2m | m → MAB 4g が必要（g≥4 は MAB 16 以上で不可） |
   | `ipassa $peid $t` | 4m+p | PE ごとに 4m / 4m+2 に割れる（不可） |
   | `ipackbit $peid $ls0 $t` | 8m+2p | 同上 |
   | `ipassa $peid $t` + `$lmt0vj1` | 4m+2（全 PE 一致） | 2m+1 → 行 1..32（**行 0 が抜ける**） |
   固定オペランドは第 1 入力のみ、A/B のメモリ語は下位ビットが常に 0 なので、
   シフト量・加算・論理和で 4m/8m を作る経路はない。
4. 唯一 T=4m を作れる 1 命令は `ipackbit $mabid $ls0 $t $mb`（T=2m と BAR0=2m を同時に書き、
   アドレス = BAR0+T = 4m にする）。意味的には正しいことを probe で確認したが、
   **アセンブラのハザード検査が通らない**:
   - BAR 書きの近傍で `gmwrite` を出すと `PortConflictError: A LM0 memory port is unavailable`
     （BAR 直後は可、2〜4 行後で失敗、実測）。B の行列書き込み 4 回が置けない。
   - T と BAR を同時に書くと T の読み出しに必要な間隔が 1 行増える（2 行 → 3 行）。
   この 2 点で 2 行以上失い、17 行を下回らない（`cand_a.vsm`〜`cand_d.vsm` はすべて assemble 不可）。
5. 放送は 1 行あたり 4 行（2 長語 `l1bmm`）が上限。行 0–3 を MAB 0 のローカル出力で賄う前提だと
   行 4–31 に 7 グループ必要で、GRF0 の読み出しが gmmul の直後でも可（実測）なので
   計算 8 行 + 放送 8 行 = 16 行が理論上限。T の設定が 1 命令になれば届くが、上記のとおり作れない。

## 候補ファイル

| file | 内容 | 結果 |
|---|---|---|
| `t17.vsm` | cand1 構成 + 正しい T（2 命令） | ACCEPTED score=17（参照） |
| `cand_a.vsm` | T=2m + BAR0=2m（T=4m）| assemble 不可（L1BM 語長・port） |
| `cand_b.vsm` | 同上、放送を 2 長語に統一 | assemble 不可（T DataRace） |
| `cand_c.vsm` | cand1 + T/BAR 同時設定 | assemble 不可（PortConflict） |
| `cand_d.vsm` | BAR を 2 行目に移動 | assemble 不可（PortConflict） |

## 結論

16 行は未達。T を 1 命令で 4m/8m にする命令が ISA に存在せず、
BAR 併用の唯一解はハザード検査（LM0 ポート競合）で 2 行以上を要求するため 17 行が下限。
