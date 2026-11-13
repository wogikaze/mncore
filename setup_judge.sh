#!/usr/bin/env bash
set -euo pipefail

TEMP_DIR=$(mktemp -d)
trap 'rm -rf "$TEMP_DIR"' EXIT
ARCHIVE="$TEMP_DIR/judge.zip"
DOWNLOAD_URL="https://mncore-challenge.preferred.jp/judge-mncore-challenge.zip"

echo "公式judgeをダウンロード中: $DOWNLOAD_URL"
curl --fail --location --silent --show-error --output "$ARCHIVE" "$DOWNLOAD_URL"
unzip -tq "$ARCHIVE"
unzip -q "$ARCHIVE" -d "$TEMP_DIR"

NEW_JUDGE="$TEMP_DIR/judge"
if [[ ! -f "$NEW_JUDGE/judge-py/judge.py" || \
      ! -x "$NEW_JUDGE/judge-py/mncore2_emuenv/assemble3" || \
      ! -x "$NEW_JUDGE/judge-py/mncore2_emuenv/gpfn3_package_main" ]]; then
    echo "エラー: judge.py、assembler、emulatorを含む公式judgeではありません" >&2
    exit 1
fi

echo "公式judgeの動作確認中..."
if [[ "$OSTYPE" == darwin* ]]; then
    (cd "$NEW_JUDGE" && ./judge example/hello_world/testcase.vsm example/hello_world/example.vsm)
else
    (cd "$NEW_JUDGE" && python3 judge-py/judge.py example/hello_world/testcase.vsm example/hello_world/example.vsm)
fi

if [[ -e ./judge ]]; then
    mv ./judge "$TEMP_DIR/previous-judge"
fi
if ! mv "$NEW_JUDGE" ./judge; then
    if [[ -e "$TEMP_DIR/previous-judge" ]]; then
        mv "$TEMP_DIR/previous-judge" ./judge
    fi
    exit 1
fi

echo "公式judgeをセットアップしました。"
