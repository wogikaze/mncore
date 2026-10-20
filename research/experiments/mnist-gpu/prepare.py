#!/usr/bin/env python3
"""Build the DRAM images for running fx_export's MNIST train step on the GPU.

The layout is the one `fx_export.mncore_utils.generate_vsm_input_commands`
writes: flatten the tensor, split it into four equal chunks, pack two float32
values per long word (first value in the high half), and place chunk g at
`base_addr` of DRAM group g.

Outputs (all little-endian u64 unless noted):

  init_dram.bin     4 x DRAM_LONGS, weights placed at their ONNX addresses
  train_inputs.bin  234 x 4 x 32768, input batch at addr 0
  train_targets.bin 234 x 4 x 32, target batch at addr 40000
  train_labels.bin  234 x 256 u8
  test_inputs.bin   39 x 4 x 32768
  test_targets.bin  39 x 4 x 32
  test_labels.bin   39 x 256 u8
  epoch_orders.bin  100 x 234 int32 batch order
  reference.npz     PyTorch weights after 0..5 steps on the same batches
"""

import json
import os
import struct

import numpy as np
import torch

from torchvision import datasets

from fx_export.train import SimpleNN1024, get_mnist_transform

DRAM_LONGS = 264064
GROUPS = 4
BATCH = 256
INPUT_FLOATS = BATCH * 1024
TARGET_FLOATS = BATCH

ADDRS = {
    "fc1_weight": (48000, 16 * 1024),
    "fc1_bias": (56000, 16),
    "fc2_weight": (64000, 16 * 16),
    "fc2_bias": (72000, 16),
    "target": (40000, TARGET_FLOATS),
}

HERE = os.path.dirname(os.path.abspath(__file__))


def pack_tensor(values: np.ndarray, base_addr: int, as_int: bool = False):
    """Return {group: (addr, words)} for a tensor written by the emulator path."""
    flat = np.ascontiguousarray(values, dtype=np.int32 if as_int else np.float32).ravel()
    n = flat.size
    if n <= 16:
        chunks = [(0, flat)]
    else:
        assert n % GROUPS == 0, n
        q = n // GROUPS
        chunks = [(g, flat[g * q:(g + 1) * q]) for g in range(GROUPS)]
    out = {}
    for g, chunk in chunks:
        if chunk.size % 2:
            chunk = np.append(chunk, np.float32(0.0))
        bits = chunk.view(np.uint32)
        words = (bits[0::2].astype(np.uint64) << np.uint64(32)) | bits[1::2]
        out[g] = (base_addr, words.astype("<u8"))
    return out


def batch_words(data: np.ndarray, base_addr: int, as_int: bool = False):
    """Four group arrays for one batch, concatenated in group order."""
    packed = pack_tensor(data, base_addr, as_int=as_int)
    per_group = packed[0][1].size
    out = np.zeros((GROUPS, per_group), dtype="<u8")
    for g in range(GROUPS):
        addr, words = packed.get(g, (base_addr, np.zeros(per_group, dtype="<u8")))
        out[g, addr - base_addr:addr - base_addr + words.size] = words
    return out


def main():
    torch.manual_seed(0)
    model = SimpleNN1024()
    model.train()

    transform = get_mnist_transform()
    train_ds = datasets.MNIST(
        "./data", train=True, download=False, transform=transform
    )
    test_ds = datasets.MNIST(
        "./data", train=False, download=False, transform=transform
    )

    def batches(dataset, shuffle, seed=0):
        gen = torch.Generator().manual_seed(seed)
        loader = torch.utils.data.DataLoader(
            dataset,
            batch_size=BATCH,
            shuffle=shuffle,
            drop_last=True,
            generator=gen if shuffle else None,
        )
        xs, ts, ys = [], [], []
        for data, target in loader:
            xs.append(data.numpy().astype(np.float32))
            ts.append(target.numpy().astype(np.float32))
            ys.append(target.numpy().astype(np.uint8))
        return xs, ts, ys

    print("building train batches", flush=True)
    train_x, train_t, train_y = batches(train_ds, True)
    print("building test batches", flush=True)
    test_x, test_t, test_y = batches(test_ds, False)

    init = np.zeros((GROUPS, DRAM_LONGS), dtype="<u8")
    for name, (addr, _n) in ADDRS.items():
        if name == "target":
            continue
        key = name.replace("_weight", ".weight").replace("_bias", ".bias")
        tensor = model.state_dict()[key].detach().numpy()
        for g, (a, words) in pack_tensor(tensor, addr).items():
            init[g, a:a + words.size] = words

    init.tofile(os.path.join(HERE, "init_dram.bin"))

    def write_batches(prefix, xs, ts, ys):
        n = len(xs)
        inputs = np.stack(
            [batch_words(x.reshape(BATCH, -1), 0) for x in xs]
        ).astype("<u8")
        targets = np.stack(
            [batch_words(t, ADDRS["target"][0], as_int=True) for t in ts]
        ).astype("<u8")
        labels = np.stack(ys)
        inputs.tofile(os.path.join(HERE, f"{prefix}_inputs.bin"))
        targets.tofile(os.path.join(HERE, f"{prefix}_targets.bin"))
        labels.tofile(os.path.join(HERE, f"{prefix}_labels.bin"))
        print(prefix, n, "batches", flush=True)

    write_batches("train", train_x, train_t, train_y)
    write_batches("test", test_x, test_t, test_y)

    # The inference program uses different addresses for the same tensors.
    infer_addrs = {
        "fc1_weight": 40000,
        "fc1_bias": 48000,
        "fc2_weight": 56000,
        "fc2_bias": 64000,
    }
    infer_init = np.zeros((GROUPS, DRAM_LONGS), dtype="<u8")
    for name, addr in infer_addrs.items():
        key = name.replace("_weight", ".weight").replace("_bias", ".bias")
        tensor = model.state_dict()[key].detach().numpy()
        for g, (a, words) in pack_tensor(tensor, addr).items():
            infer_init[g, a:a + words.size] = words
    infer_init[:, 0:INPUT_FLOATS // 2 // GROUPS] = batch_words(
        train_x[0].reshape(BATCH, -1), 0
    )
    infer_init.tofile(os.path.join(HERE, "init_infer.bin"))

    rng = np.random.default_rng(0)
    orders = np.stack([rng.permutation(len(train_x)) for _ in range(100)]).astype("<i4")
    orders.tofile(os.path.join(HERE, "epoch_orders.bin"))

    # Reference trajectory: the same batches and init through plain PyTorch SGD.
    ref = {"init": {k: v.detach().clone().numpy() for k, v in model.state_dict().items()}}
    optimizer = torch.optim.SGD(model.parameters(), lr=0.01)
    criterion = torch.nn.CrossEntropyLoss()
    for step in range(5):
        data = torch.from_numpy(train_x[step])
        target = torch.from_numpy(train_t[step]).long()
        optimizer.zero_grad()
        loss = criterion(model(data), target)
        loss.backward()
        optimizer.step()
        ref[f"step{step + 1}"] = {
            k: v.detach().clone().numpy() for k, v in model.state_dict().items()
        }
        print(f"reference step {step + 1}: loss {loss.item():.6f}", flush=True)
    np.savez(os.path.join(HERE, "reference.npz"), **{
        f"{step}_{k}": v for step, weights in ref.items() for k, v in weights.items()
    })

    meta = {
        "dram_longs": DRAM_LONGS,
        "groups": GROUPS,
        "batch": BATCH,
        "addrs": {k: v[0] for k, v in ADDRS.items()},
        "train_batches": len(train_x),
        "test_batches": len(test_x),
        "test_samples": len(test_x) * BATCH,
    }
    with open(os.path.join(HERE, "meta.json"), "w") as f:
        json.dump(meta, f, indent=2)
    print(json.dumps(meta, indent=2))


if __name__ == "__main__":
    main()
