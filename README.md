# smcTuring — mov-only Turing Machine

Code supplement to the published research paper:

> **Pure Infinitely Self-Modifying Code is Realizable and Turing-complete**  
> Gregory Morse — *International Journal of Electronics and Telecommunications*, Vol. 64 No. 2, 2018  
> DOI: [10.24425/119359](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359)

---

## Overview

This project provides a working implementation of a Turing machine whose simulation loop
is expressed exclusively using `mov` instructions — no arithmetic, no branches, no
comparisons. This is possible because of Stephen Dolan's result that `mov` alone is
Turing-complete, requiring only three addressing modes:

| Mode | Syntax |
|---|---|
| Load immediate | `mov Rdest, c` |
| Load indexed | `mov Rdest, [Rsrc + Roffset]` |
| Store indexed | `mov [Rdest + Roffset], Rsrc` |

The paper extends this to *self-modifying code*, showing that a code-only model in which
every instruction only modifies other instructions is itself Turing-complete — a pure form
of infinitely self-modifying code that achieves general computation without any classical
control-flow instructions.

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

### `MovTM` — mov-only Turing Machine

| Variant | Flag | Notes |
|---|---|---|
| Inline x86 | `1` | MSVC inline `__asm`; x86 only; pure `mov` loop |
| External | `2` | MASM `MovTM`; x86 and x64; pure `mov` loop |
| C emulation | `4` | C translation of the `mov`-only data-driven dispatch |

The `MovTM` assembly procedures contain **no** `jmp`, `cmp`, `add`, `call`, or any
instruction other than `mov`. Branching and symbol comparison are achieved entirely through
indexed memory access into a scratch array that acts as a comparison selector.

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

## License

The code in this repository is released as open-source to accompany the above publication.
The paper itself is published under a
[Creative Commons Attribution-NonCommercial 4.0 International](https://creativecommons.org/licenses/by-nc/4.0/)
licence.
