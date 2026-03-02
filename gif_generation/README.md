# GIF生成ワークフロー

`gif_generation/` 以下に GIF 生成に関わるスクリプト、ローカルビューア、成果物を集約しました。ここでは運用手順と主要な環境変数をまとめています。

## ディレクトリ構成

- `gif_generation/record_animation.js` — Puppeteer で録画・GIF 化するメインスクリプト。
- `gif_generation/download_memory_animations.py` — メモリアニメーション (.smv) の一括ダウンロード。
- `gif_generation/local_viewer/` — HTTP サーバで配信するローカルビューア一式。
- `gif_generation/mncore_memory_movies/` — `.smv` / `.deflate` を保管（ダウンロードスクリプトの既定出力先）。
- `gif_generation/gif_frames/` — 一時的な PNG フレーム置き場。
- `gif_generation/memory_animation_gifs/` — 生成済み GIF の保存先。

## 1. ローカルビューアの起動

```
npx --yes http-server gif_generation/local_viewer -p 4173 -c-1
```

## 2. 収録（例）

```
MNCORE_CAPTURE_MS=120000 \
MNCORE_PLAYBACK_SPEED=0.30 \
MNCORE_CAPTURE_FPS=30 \
node gif_generation/record_animation.js
```

- `MNCORE_CAPTURE_MS`: 最大録画時間（ミリ秒）。終端検知で早めに停止。
- `MNCORE_PLAYBACK_SPEED`: ビューア速度スライダ (0.0〜1.0)。
- `MNCORE_CAPTURE_FPS`: `canvas` から取得するフレームレート。
- `MNCORE_END_BUFFER_FRAMES`: 終端検知後の追加フレーム数。
- `MNCORE_CAPTURE_ALL=1`: すべての命令×映画バリエーションを一括で録画＋GIF 化。
- `MNCORE_GIF_ROOT`: GIF 保存先ルート（既定 `gif_generation/memory_animation_gifs/`）。
- `MNCORE_KEEP_FRAMES=1`: GIF 化後も PNG を残す。
- `MNCORE_SKIP_EXISTING=0`: 既存 GIF があっても再生成。
- `MNCORE_NAV_TIMEOUT`: `page.goto` などのタイムアウト値（ms）。
- `MNCORE_CAPTURE_SCALE`: Puppeteer のデバイススケール (1.0=既定)。文字を大きく鮮明にしたい場合は 2 以上に設定。

## 3. パレット生成 & GIF 手動変換

```
ffmpeg -y -framerate 30 -i gif_generation/gif_frames/frame_%04d.png -vf palettegen gif_generation/gif_frames/palette.png
ffmpeg -y -framerate 30 -i gif_generation/gif_frames/frame_%04d.png -i gif_generation/gif_frames/palette.png -lavfi paletteuse gif_generation/memory_animation_gifs/dram_to_l2bm_ingroup_bcast.gif
```

必要に応じて `-framerate` や出力パスを調整してください。
