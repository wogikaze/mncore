# MN-Core VSM syntax for VS Code

`.vsm` (MN-Core 2 アセンブリ) 用の TextMate 文法。

## 色分け

| 対象 | 例 | 色 (Dark+ 前提, `vsm-colors.json`) |
|---|---|---|
| imm | `imm ui"0x4b400000"` | 紫 (即値は薄緑) |
| ALU 命令 | `ior` `fmin` `ffloor` `ullsr` | 青・太字 |
| MAU 命令 | `fvfma` `fvadd` `dmread` | 黄・太字 |
| 転送命令 | `l1bmr4lbor` `l2bmd` `mvd` `mvp` | 青緑・太字 |
| `nop` | | 灰・斜体 |
| `;`（同じ語に入る式の区切り） | | 橙・太字 |
| GRF0 | `$lr16` `$r65` | 橙 |
| GRF1 | `$ls72` `$s64` | 水色 |
| LM1 | `$ln4` `$n0` | 薄紫 |
| LM0 / T 間接 / T | `$lm[...]` `$lmt4` `$t` | 赤 (T 系は下線) |
| フォワーディング | `$aluf` `$mauf` `$mreadf` | 金・太字斜体 |
| `$nowrite` | | 暗灰・斜体 |
| マスク | `$omr1` `/$imr2` | 赤・太字 |
| アドレス修飾 | `v` `v2` `v4` `e` | 灰青・斜体 |
| 符号反転 | `-$x` の `-` | 赤 |
| 固定 ID | `$subpeid` `$mabid` | 青緑・斜体 |
| コメント | `# ...` | 緑。コメント中の `$レジスタ` も同じ色分け、`[42]` の行番号タグは太字、`段 A:` などの見出しは明るい緑 |

## インストール

```bash
cd tools/vscode-vsm
npx @vscode/vsce package --allow-missing-repository   # vsm-syntax-0.1.2.vsix ができる
code --install-extension vsm-syntax-0.1.2.vsix
```

`.vsm` ではタブ幅 4 が既定になる（`tools/vsmfmt.py --tabs 4` の出力がそろって見える）。

文法だけでもテーマの標準色で色は付く。上の表の配色にするには
`vsm-colors.json` の中身を settings.json の
`"editor.tokenColorCustomizations"` に入れる
（このリポジトリでは `.vscode/settings.json` に設定済み。`.vscode/` は gitignore 対象）。

スコープ名の末尾はすべて `.vsm` なので、ほかの言語の色には影響しない。
