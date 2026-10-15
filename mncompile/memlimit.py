"""Keep compiler processes from exhausting the machine's memory.

A compile tries many candidate programs; a few strategies can build very large
intermediate programs. Under WSL an out-of-memory machine takes the whole VM
down, so compiler processes run with a soft data-size limit: exceeding it
raises MemoryError, which the compiler treats as a rejected candidate. Child
processes (assembler, emulators, judge) are started with the limit lifted.
"""

from __future__ import annotations

import os
import resource


def total_memory() -> int:
    """Physical memory in bytes."""
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemTotal:"):
                    return int(line.split()[1]) * 1024
    except OSError:
        pass
    return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")


def limit_process(fraction: float) -> int:
    """Cap this process's data segment at `fraction` of physical memory (soft limit); returns bytes."""
    limit = int(total_memory() * fraction)
    soft, hard = resource.getrlimit(resource.RLIMIT_DATA)
    if hard != resource.RLIM_INFINITY:
        limit = min(limit, hard)
    resource.setrlimit(resource.RLIMIT_DATA, (limit, hard))
    return limit


def lift_for_child():
    """preexec_fn for subprocesses: restore the soft limit to the hard limit."""
    soft, hard = resource.getrlimit(resource.RLIMIT_DATA)
    resource.setrlimit(resource.RLIMIT_DATA, (hard, hard))


def default_jobs(per_job_gib: float = 1.8) -> int:
    """Parallel compiles that fit in memory with `per_job_gib` each (and in the CPUs)."""
    by_mem = int(total_memory() * 0.75 / (per_job_gib * 2**30))
    return max(1, min(os.cpu_count() or 1, by_mem))
