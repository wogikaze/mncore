"""Generic MN-Core 2 compiler for ordinary Python kernels with layout contracts."""

from .compiler import Compilation, compile_program
from .errors import CompileError
from .layout import Contract, TensorSpec, parse_layout, parse_tensor

__all__ = ["Compilation", "CompileError", "Contract", "TensorSpec", "compile_program", "parse_layout", "parse_tensor"]
