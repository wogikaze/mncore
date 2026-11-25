"""Compiles small MLSDK (SDK 0.9) workloads for the emu2 backend and keeps the VSM.

Run inside the mncore-sdk-minimal:0.9 image (see run_compile.sh):
    python3 compile_workloads.py OUT_DIR
Each workload is compiled into OUT_DIR/<name>/ (MLSDK codegen directory with
model.vsm.zst) and run once on emu2 so that compilation is complete.
"""
import sys

import torch
from mlsdk import (
    CacheOptions,
    Context,
    MNCoreSGD,
    MNDevice,
    set_buffer_name_in_optimizer,
    set_tensor_name_in_module,
    storage,
)


def compile_fn(context, name, fn, sample, out, options=None):
    kwargs = {"options": options} if options else {}
    f = context.compile(
        fn,
        sample,
        storage.path(f"{out}/{name}"),
        cache_options=CacheOptions(f"{out}/{name}_cache"),
        **kwargs,
    )
    f(sample)
    print(f"compiled {name}")


def main():
    out = sys.argv[1]
    torch.manual_seed(0)
    context = Context(MNDevice("emu2"))
    Context.switch_context(context)

    compile_fn(context, "add", lambda i: {"out": i["x"] + i["y"]},
               {"x": torch.randn(64, 64), "y": torch.randn(64, 64)}, out)
    compile_fn(context, "softmax", lambda i: {"out": torch.softmax(i["x"], dim=-1)},
               {"x": torch.randn(64, 64)}, out)
    compile_fn(context, "matmul", lambda i: {"out": i["a"] @ i["b"]},
               {"a": torch.randn(256, 256), "b": torch.randn(256, 256)}, out)

    class Mlp(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.fc1 = torch.nn.Linear(64, 64)
            self.fc2 = torch.nn.Linear(64, 16)

        def forward(self, *, x):
            return {"y": self.fc2(torch.relu(self.fc1(x)))}

    model = Mlp()
    set_tensor_name_in_module(model, "mlp_fwd")
    for p in model.parameters():
        context.register_param(p)
    model.eval()
    compile_fn(context, "mlp_fwd", lambda i: model(**i), {"x": torch.randn(64, 64)}, out)

    train_model = Mlp()
    train_model.train()
    set_tensor_name_in_module(train_model, "mlp_train")
    for p in train_model.parameters():
        context.register_param(p)
    optimizer = MNCoreSGD(train_model.parameters(), 0.01, 0.9, 0.0)
    set_buffer_name_in_optimizer(optimizer, "optim0")
    context.register_optimizer_buffers(optimizer)

    def train_step(inp):
        optimizer.zero_grad()
        loss = ((train_model(x=inp["x"])["y"] - inp["t"]) ** 2).mean()
        loss.backward()
        optimizer.step()
        return {"loss": loss}

    compile_fn(context, "mlp_train", train_step,
               {"x": torch.randn(64, 64), "t": torch.randn(64, 16)}, out)


if __name__ == "__main__":
    main()
