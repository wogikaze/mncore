#!/bin/bash
# Runs an MN-Core SDK 0.9 tool (assemble3 or gpfn3_package_main) inside the SDK image.
# Paths must be under /home (bind-mounted at the same location).
tool=$1; shift
exec docker run --rm -v /home:/home -w "$PWD" mncore-sdk-minimal:0.9 /opt/pfn/pfcomp/codegen/build/tools/$tool "$@"
