---
title: assemble3
id: 66b970163e19f0001c36f4ca
created_unix: 1723428888
updated_unix: 1723429731
views: 28
---

# assemble3

[[MN-Core]]の[[アセンブラ]]
 [[2.2 アセンブラ]]

$ assemble3 --help
```--help
usage: assemble
    [-h] [--print-asm] [--print-comment] [--print-asm-version]
    [--input-type INPUT_TYPE]
    [--output-file OUTPUT_FILE] [--disable-hazard-checker] [--(no-)packer]
    SOURCE_FILE

required arguments
    SOURCE_FILE                 Path of source vsm file

optional arguments
    -h, --help                      Show this help message and exit
    
    --print-asm                     Print vsm source code
    --print-comment                 Print all vsm comment lines
    --print-csv                     Print csv instead of normal output
    --print-asm-version             Print assembler version (Git revision) as comment
    
    --input-type INPUT_TYPE         Input file type. vsm: default, asm: (un)aligned i/m file
    --output-file OUTPUT_FILE       Path of output asm file
    
    --enable-hazard-checker         Enable hazard checker (default)
    --disable-hazard-checker        Disable hazard checker
    --hazard-check-warning          Hazard checker report error as warning
    --enable-deadlock-checker       Enable deadlock checker (default)
    --disable-deadlock-checker      Disable deadlock checker
    --deadlock-check-warning        Deadlock checker report error as warning
    --enable-mv-completion-checker  Enable MV completion checker. Means --enable-deadlock-checker
    --enable-tag-checker            Enable tag checker (not yet implemented)
    --disable-tag-checker           Disable tag checker (default)
    --enable-mv-checker             Enable mv checker
    --disable-mv-checker            Disable mv checker (default)
    --mv-check-warning              Mv checker report error as warning
    
    --instruction-mode MODE         Instruction mode (flat / auto_stride(default)).
    --packer                        Apply packer (default for q-instruction/loader mode)
    --disable-packer                Don't apply packer (default for plain/csv mode)
    --q-instruction                 Output result as q instructions.
    --loader                        Output result in loader format (must use with --output-file option)
                                    When you specify --output-file hoge --loader,
                                    this option makes hoge.idma.inst, hoge.idma.inst.txt, hoge.idma.dat,
                                    hoge.ddma.inst, hoge.ddma.inst.txt, and hoge.ddma.dat.
    --binary                        Output result as binary (implies --packer and --instruction-mode flat)
    --alignment ALIGN               Align instruction block for optimizing idma2 burst request.
    --ll-mode MODE                  Specify ll bits. cold: 0b01 (default), hot: 0b11, mix: mix of cold and hot.
                                    This options is intended to be used for verification.
    --insert-nop                    This option inserts a nop on each line.
    --ignore-contextual-error       Skip error checking depends on context

```
