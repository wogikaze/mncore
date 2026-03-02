#!/usr/bin/env python3
"""Download and decompress all MN-Core memory animation movies."""
from __future__ import annotations

import argparse
import pathlib
import re
import sys
import urllib.parse
import urllib.request
import zlib
from typing import Iterable, List

BASE_URL = "https://mncore-challenge.preferred.jp/memory-animation/mov/"
ANIMATION_NAMES: List[str] = [
    "DRAM\u2192L2BM ingroup-bcast",
    "DRAM\u2192L2BM intergroup-bcast",
    "DRAM\u2192L2BM intergroup-distrib-bcast",
    "DRAM\u2192L2BM parallel-unicast",
    "DRAM\u2192L2BM single-unicast",
    "DRAM\u2192PDM concat",
    "DRAM\u2192PDM single-unicast",
    "L1BM\u2192L1BM multicast",
    "L1BM\u2192L2BM concat",
    "L1BM\u2192L2BM concat-reduce",
    "L1BM\u2192L2BM reduce",
    "L1BM\u2192L2BM single-unicast",
    "L1BM\u2192MAB16x1 bcast",
    "L1BM\u2192MAB4x4 bcast",
    "L1BM\u2192PE bcast",
    "L1BM\u2192PE distrib",
    "L2BM\u2192DRAM ingroup-reduce",
    "L2BM\u2192DRAM intergroup-concat-reduce",
    "L2BM\u2192DRAM intergroup-reduce",
    "L2BM\u2192DRAM parallel-unicast",
    "L2BM\u2192DRAM single-unicast",
    "L2BM\u2192L1BM bcast",
    "L2BM\u2192L1BM distrib",
    "L2BM\u2192L1BM distrib-bcast",
    "L2BM\u2192PDM concat",
    "L2BM\u2192PDM ingroup-reduce",
    "L2BM\u2192PDM intergroup-reduce",
    "L2BM\u2192PDM parallel-unicast",
    "L2BM\u2192PDM single-unicast",
    "MAB16x1\u2192L1BM reduce",
    "MAB16x1\u2192L1BM single-unicast",
    "MAB4x4\u2192L1BM reduce",
    "MAB4x4\u2192L1BM single-unicast",
    "MAU matrix-mult",
    "MAU\u2192PE matrix-read",
    "PDM\u2192DRAM distrib",
    "PDM\u2192DRAM single-unicast",
    "PDM\u2192L2BM distrib",
    "PDM\u2192L2BM intergroup-bcast",
    "PDM\u2192L2BM parallel-unicast",
    "PDM\u2192L2BM single-unicast",
    "PDM\u2192PDM single-unicast",
    "PE\u2192L1BM concat",
    "PE\u2192MAU matrix-write",
    "PE\u2192MAU\u2192PE matrix-transpose",
]


def slugify(name: str) -> str:
    """Convert an animation name into a filesystem-friendly slug."""
    slug = name.replace("\u2192", "-to-")
    slug = slug.lower()
    slug = re.sub(r"[^0-9a-z]+", "_", slug)
    slug = slug.strip("_")
    return slug or "animation"


def iter_requested(names: Iterable[str], filters: Iterable[str] | None) -> List[str]:
    if not filters:
        return list(names)
    needles = [f.lower() for f in filters]
    selected = []
    for name in names:
        lowered = name.lower()
        if any(n in lowered for n in needles):
            selected.append(name)
    return selected


def download_one(name: str, out_dir: pathlib.Path, keep_compressed: bool, skip_existing: bool) -> None:
    slug = slugify(name)
    smv_path = out_dir / f"{slug}.smv"
    compressed_path = out_dir / f"{slug}.deflate"

    if skip_existing and smv_path.exists():
        print(f"[skip] {name} (already downloaded)")
        return

    encoded = urllib.parse.quote(name, safe="")
    url = BASE_URL + encoded
    req = urllib.request.Request(url, headers={"User-Agent": "mncore-downloader/1.0"})
    print(f"[fetch] {name}")
    with urllib.request.urlopen(req) as resp:
        compressed = resp.read()

    if keep_compressed:
        compressed_path.write_bytes(compressed)

    try:
        decompressed = zlib.decompress(compressed)
    except zlib.error:
        # Fallback for raw-deflate streams just in case.
        decompressed = zlib.decompress(compressed, -zlib.MAX_WBITS)

    if not decompressed.startswith(b"smv"):
        raise RuntimeError(f"Unexpected payload for {name}; header={decompressed[:8]!r}")

    smv_path.write_bytes(decompressed)
    size_kib = len(decompressed) / 1024
    print(f"  -> wrote {smv_path.name} ({size_kib:.1f} KiB)")


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    default_output = pathlib.Path(__file__).resolve().parent / "mncore_memory_movies"
    parser.add_argument(
        "-o",
        "--output",
        type=pathlib.Path,
        default=default_output,
        help=(
            "directory to store the downloaded .smv files "
            f"(default: {default_output})"
        ),
    )
    parser.add_argument(
        "--only",
        nargs="*",
        help="case-insensitive substrings to select a subset of animations",
    )
    parser.add_argument(
        "--keep-compressed",
        action="store_true",
        help="also save the original deflate blob next to each .smv",
    )
    parser.add_argument(
        "--skip-existing",
        action="store_true",
        help="do not re-download animations whose .smv file already exists",
    )
    args = parser.parse_args(argv)

    args.output.mkdir(parents=True, exist_ok=True)
    targets = iter_requested(ANIMATION_NAMES, args.only)
    if not targets:
        print("No animations matched the provided filters", file=sys.stderr)
        return 1

    print(f"Will download {len(targets)} animation(s) into {args.output.resolve()}")
    for name in targets:
        try:
            download_one(name, args.output, args.keep_compressed, args.skip_existing)
        except Exception as exc:  # noqa: BLE001
            print(f"[error] {name}: {exc}", file=sys.stderr)
            return 2

    print("All requested animations downloaded.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
