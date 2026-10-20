#!/usr/bin/env python3
"""Load the four parameter tensors from a GPU DRAM dump and score MNIST."""

import sys

import numpy as np
import torch
from torchvision import datasets

from fx_export.train import SimpleNN1024, get_mnist_transform

GROUPS = 4
DRAM_LONGS = 264064
ADDRS = {
    "fc1.weight": (48000, 16 * 1024),
    "fc1.bias": (56000, 16),
    "fc2.weight": (64000, 16 * 16),
    "fc2.bias": (72000, 16),
}


def unpack(dram, addr, count):
    if count <= 16:
        spans = [(0, (count + 1) // 2)]
    else:
        per_group = count // GROUPS
        spans = [(g, per_group // 2) for g in range(GROUPS)]
    parts = []
    for g, longs in spans:
        words = dram[g, addr:addr + longs]
        bits = np.empty(2 * longs, dtype=np.uint32)
        bits[0::2] = (words >> np.uint64(32)).astype(np.uint32)
        bits[1::2] = (words & np.uint64(0xFFFFFFFF)).astype(np.uint32)
        parts.append(bits.view(np.float32))
    return np.concatenate(parts)[:count]


def main(path: str):
    dram = np.fromfile(path, dtype="<u8").reshape(GROUPS, DRAM_LONGS)
    model = SimpleNN1024()
    for name, (addr, count) in ADDRS.items():
        value = unpack(dram, addr, count).reshape(model.state_dict()[name].shape)
        model.state_dict()[name].copy_(torch.from_numpy(value.copy()))
    model.eval()

    test = datasets.MNIST(
        "./data", train=False, download=False, transform=get_mnist_transform()
    )
    loader = torch.utils.data.DataLoader(test, batch_size=1000)
    correct = total = 0
    with torch.no_grad():
        for data, target in loader:
            correct += (model(data).argmax(1) == target).sum().item()
            total += target.numel()
    print(f"{path}: test accuracy {100.0 * correct / total:.2f}% ({correct}/{total})")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "research/experiments/mnist-gpu/final_dram.bin")
