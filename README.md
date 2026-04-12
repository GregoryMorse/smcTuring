# smcTuring — Pure Infinitely Self-Modifying Code Turing Machine

[![DOI](https://img.shields.io/badge/DOI-10.24425%2F119359-blue)](https://doi.org/10.24425/119359)
[![IJET](https://img.shields.io/badge/Journal-IJET_Vol._64_No._2_%282018%29-green)](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/License-CC_BY--NC_4.0-lightgrey.svg)](https://creativecommons.org/licenses/by-nc/4.0/)

Code supplement to the published research paper:

> **Pure Infinitely Self-Modifying Code is Realizable and Turing-complete**  
> Gregory Morse — *International Journal of Electronics and Telecommunications*, Vol. 64 No. 2, 2018  
> DOI: [10.24425/119359](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359)
>
> Presented at the 17th Central European Conference on Cryptology ([CECC’17](https://cecc17.tele.pw.edu.pl/index.php/technical-program/program)), Warsaw, Poland, June 28, 2017.

---

## Overview

This project is a working demonstration that *pure infinitely self-modifying code* (pure
SMC) is Turing-complete. In the pure SMC model every instruction in the simulation loop
exists solely to rewrite the operands of other instructions — the code never performs
arithmetic, branching, or comparison directly. Computation emerges entirely from the code
rewriting itself on every iteration, indefinitely.

The sole instruction used is `mov`. This is not incidental: `mov` is the natural primitive
for pure SMC because it can write to any memory address, including the code segment, making
it the only general instruction through which one instruction can directly rewrite another.
This is a **distinct result** from Dolan's 2013 proof that `mov` alone is Turing-complete.
Dolan's construction uses a *static* body of `mov` instructions and achieves
Turing-completeness through data-driven dispatch, with no self-modification whatsoever.
Here the code is never static: every `mov` in the loop rewrites the operands of subsequent
`mov` instructions before they execute. Dolan's result supplies the theoretical foundation;
the pure SMC model — that a code-only, infinitely self-rewriting program can achieve
general computation — is the paper's own contribution.

Three `mov` addressing modes are used:

| Mode | Syntax |
|---|---|
| Load immediate | `mov Rdest, c` |
| Load indexed | `mov Rdest, [Rsrc + Roffset]` |
| Store indexed | `mov [Rdest + Roffset], Rsrc` |

## Background

- S. Dolan, *mov is Turing-complete*, University of Cambridge Computer Laboratory, Technical Report, 2013.  
  <https://www.cl.cam.ac.uk/~sd601/papers/mov.pdf>
- The M/O/Vfuscator — a compiler that emits only `mov` instructions:  
  <https://github.com/xoreaxeaxeax/movfuscator>

## Repository Structure

```
smcTuring/
├── main.cpp          # Driver: constructs the TM, runs all variants, benchmarks
├── tm.asm            # MASM external assembly — MovTM, AsmTM, AsmListTM (x86 & x64)
└── smcTuring.vcxproj # Visual Studio project (Win32 / x64, Debug / Release)
```

## Implementations

Three independent Turing machine simulators are provided, each demonstrated with the same
input and benchmarked head-to-head:

### `CTM` — Pure C

| Variant | Description |
|---|---|
| Limited (`LimUnlim & 1`) | Flat byte array for transitions; fixed state encoding; one-sided tape |
| General (`LimUnlim & 2`) | Linked-list transitions; pointer-based next-state resolution; two-sided tape |

### `AsmTM` — Assembly (classical TM — allows all instructions)

| Variant | Flag | Notes |
|---|---|---|
| Inline x86 — limited | `1` | MSVC inline `__asm`; x86 only |
| External — limited | `2` | MASM `AsmTM`; x86 and x64 |
| Inline x86 — general | `4` | MSVC inline `__asm`; x86 only |
| External — general | `8` | MASM `AsmListTM`; x86 and x64 |

### `MovTM` — Pure Self-Modifying `mov`-only Turing Machine

| Variant | Flag | Notes |
|---|---|---|
| Inline x86 | `1` | MSVC inline `__asm`; x86 only; pure `mov` loop |
| External | `2` | MASM `MovTM`; x86 and x64; pure `mov` loop |
| C emulation | `4` | C translation of the pure SMC `mov`-only simulation |

The `MovTM` assembly procedures contain **no** `jmp`, `cmp`, `add`, `call`, or any
instruction other than `mov`. Unlike Dolan's static `mov`-only programs, the loop body is
never static: each iteration the active `mov` instructions rewrite the immediate operands
of subsequent `mov` instructions, so the encoded bytes of the loop differ from one step to
the next. Symbol comparison is mediated by indexed memory access into a scratch array that
acts as a selector, with the result written directly back into the instruction stream —
there is no separate control-flow mechanism; the self-modification *is* the control flow.

## Turing Machine Example

The bundled Turing machine operates on an input tape of the form `<A>_<B>_` where `A` and
`B` are unsigned binary integers. While `B` is non-zero the machine decrements `B` and
increments `A`, effectively computing `A' = A + B` (binary addition by repeated
increment/decrement). The transition table is kept sorted by state so that `bsearch` can
locate the entry point for any given state at setup time.

```
Input:  0100_1001_   (A = 4, B = 9)
Output: 1101_0000_   (A = 13, B = 0)
```

## Requirements

- **Windows** (x86 or x64)
- **Visual Studio 2022 or later** (developed and tested on VS 2026 Enterprise) with:
  - MSVC C++ compiler (`cl.exe`)
  - MASM assembler (`ml.exe` / `ml64.exe`)
  - Windows 10 SDK (any version — post-build paths resolve via MSBuild properties)
- The Debug post-build step copies `ucrtbased.dll` and `vcruntime140d.dll` next to the
  executable so the binary is self-contained when run outside the IDE.

## Building

Open `smcTuring/smcTuring.vcxproj` (or the solution file) in Visual Studio and build the
desired configuration, or from a Developer Command Prompt:

```bat
msbuild smcTuring\smcTuring.vcxproj /p:Configuration=Debug /p:Platform=x64
```

Supported configurations: `Debug|Win32`, `Release|Win32`, `Debug|x64`, `Release|x64` —
all four are confirmed working.

> **Notes**
> - Inline assembly variants (`InExAsmC & 1` / `InExLimUnlim & 1|4`) are compiled only
>   for Win32 (x86) because MSVC does not support `__asm` in 64-bit mode. The external
>   MASM procedures (`tm.asm`) cover both architectures.
> - **Release|Win32 runs with optimisation disabled (`/Od`) and frame-pointer omission
>   disabled (`/Oy-`).** MSVC's optimiser (`/O2`/`/Ox`) breaks the inline `mov`-TM
>   loop in two compounding ways: (1) it can treat the `scratch[256]` stack array as
>   dead (never read by C++ code) and fail to allocate it, causing the inline assembly
>   to write into unallocated stack space; (2) with FPO active it may recruit `ebx` as
>   a virtual frame base while the assembly loop freely modifies `ebx` through the `Y`
>   register alias, corrupting the frame. Neither `/Oy-` alone nor a scoped
>   `#pragma optimize("y", off)` is sufficient — the only reliable fix is full `/Od`.
>   All other configurations (Debug|Win32, Debug|x64, Release|x64) use their standard
>   optimisation settings.

## Sample Output

x64 (external assembly + C variants):
```
C Turing machine limited transitions:     0100_1001_ -> 1101_0000_
C Turing machine:                         0100_1001_ -> 1101_0000_
External assembly Turing machine limited: 0100_1001_ -> 1101_0000_
External assembly Turing machine:         0100_1001_ -> 1101_0000_
External assembly mov Turing machine:     0100_1001_ -> 1101_0000_
C mov Turing machine:                     0100_1001_ -> 1101_0000_
```

Win32 (x86) adds inline assembly variants:
```
Inline assembly Turing machine limited:   0100_1001_ -> 1101_0000_
Inline assembly Turing machine:           0100_1001_ -> 1101_0000_
Inline assembly mov Turing machine:       0100_1001_ -> 1101_0000_
```

Benchmark (100 000 iterations, Release|x64 build, indicative):
```
C Turing machine:                              0.xxxxxx seconds
C Turing machine limited transitions:          0.xxxxxx seconds
External assembly Turing machine:              0.xxxxxx seconds
External assembly Turing machine limited:      0.xxxxxx seconds
External assembly mov Turing machine:          0.xxxxxx seconds
C mov Turing machine:                          0.xxxxxx seconds
```

## Author

**Gregory Morse**  
Eötvös Loránd University  
ORCID: [0000-0002-0231-6557](https://orcid.org/0000-0002-0231-6557)  
GitHub: [@GregoryMorse](https://github.com/GregoryMorse)  
Email: <gregory.morse@live.com>

## Citation

If you use this work, please cite the paper:

Morse, G. (2018). Pure Infinitely Self-Modifying Code is Realizable and Turing-complete.
*International Journal of Electronics and Telecommunications*, vol. 64, no. 2.
Polish Academy of Sciences. DOI: [10.24425/119359](https://doi.org/10.24425/119359)

Presented at the 17th Central European Conference on Cryptology (CECC’17),
Warsaw, Poland, June 28, 2017.
[Technical programme](https://cecc17.tele.pw.edu.pl/index.php/technical-program/program)

```bibtex
@ARTICLE{MorseGregoryPure2018,
  author    = {Morse, Gregory},
  title     = {Pure Infinitely Self-Modifying Code is Realizable and Turing-complete},
  journal   = {International Journal of Electronics and Telecommunications},
  volume    = {vol. 64},
  number    = {No 2},
  year      = {2018},
  publisher = {Polish Academy of Sciences Committee of Electronics and Telecommunications},
  doi       = {10.24425/119359},
  url       = {http://www.czasopisma.pan.pl/Content/103840/PDF/18_1151-4306-1-PB.pdf},
  keywords  = {x86, x86-64, assembly language, self-modifying code,
               Turing-completeness, code obfuscation},
  note      = {SCImago Q3},
  howpublished = {online},
  type      = {Artykuły / Articles},
  abstract  = {Although self-modifying code has been shyed away from due to its
               complexity and discouragement due to safety issues, it nevertheless
               provides for a very unique obfuscation method and a different perspective
               on the relationship between data and code. The generality of the von
               Neumann architecture is hardly realized by today's processor models. A
               code-only model is shown where every instruction merely modifies other
               instructions yet achieves the ability to compute and Turing machine
               operation is easily possible.}
}
```

## License

The code in this repository is released as open-source to accompany the above publication.
The paper itself is published under a
[Creative Commons Attribution-NonCommercial 4.0 International](https://creativecommons.org/licenses/by-nc/4.0/)
licence.
