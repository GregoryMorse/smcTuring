# smcTuring — Pure Infinitely Self-Modifying Code Turing Machine

[![DOI](https://img.shields.io/badge/DOI-10.24425%2F119359-blue)](https://doi.org/10.24425/119359)
[![IJET](https://img.shields.io/badge/Journal-IJET_Vol._64_No._2_%282018%29-green)](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359)
[![Code license: CC0 1.0](https://img.shields.io/badge/Code_license-CC0_1.0-lightgrey.svg)](LICENSE.txt)
[![CMake](https://github.com/GregoryMorse/smcTuring/actions/workflows/cmake.yml/badge.svg)](https://github.com/GregoryMorse/smcTuring/actions/workflows/cmake.yml)

Code supplement to the published research paper:

> **Pure Infinitely Self-Modifying Code is Realizable and Turing-complete**  
> Gregory Morse — *International Journal of Electronics and Telecommunications*, Vol. 64 No. 2, 2018  
> DOI: [10.24425/119359](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359)
>
> Presented at the 17th Central European Conference on Cryptology ([CECC’17](https://cecc17.tele.pw.edu.pl/index.php/technical-program/program)), Warsaw, Poland, June 28, 2017.

---

## Overview

This repository accompanies the published pure self-modifying code construction.
It contains working C++/MASM comparison simulators, a corrected SMC storage
primitive, and a complete Lean formalization of the corrected mathematical
construction with explicitly conditional bounded native refinements.

The reference `MovTM` uses a static MOV-based computation body with conventional
loop and exit branches. It rewrites allocated transition/tape data rather than
instruction operands. The paper's pure SMC construction instead requires every
executed computational instruction to write code; its primitives also use
exchanges, memory-writing arithmetic, and code-backed calls.

The original reference source passed rebuilds and output checks in all four
Win32/x64 Debug/Release configurations. The corrected `DEFADDR` primitive is in
[smcTuring/pure_smc.inc](smcTuring/pure_smc.inc). Lean proves its original/corrected
boundary equivalence and strict code-write property under explicit code-field
assumptions. Native tests cover both architectures and exact self-aliasing.

The Lean formalization proves universality, instruction-level pure code writes
and unbounded code changes in the ideal unbounded machine model. Native x86/x64
and COFF refinements state the finite-address, permission and instruction-fetch
assumptions explicitly. See the [theorem map](lean/FINAL_THEOREM_MAP.md),
[physical contract](lean/PHYSICAL_BINDING_CONTRACT.md) and
[verification evidence](lean/acceptance/execution-revision.json).

Registered as [PALOMAR-2026-10-13-000008, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-13-000008&version=1).

The paper corrections are available as a [two-page errata PDF](output/pdf/morse-2018-errata.pdf),
[LaTeX source](lean/errata/morse-2018-errata.tex) and
[minimal diff](lean/errata/morse-2018-minimal.diff). For builds and checks, see the
[Lean guide](lean/README.md) and [validation instructions](validation/README.md).

The MOV foundation uses three addressing forms:

| Mode | Syntax |
|---|---|
| Load immediate | `mov Rdest, c` |
| Load indexed | `mov Rdest, [Rsrc + Roffset]` |
| Store indexed | `mov [Rdest + Roffset], Rsrc` |

## Lean formalization of Stephen Dolan's *mov is Turing-complete*

This repository also contains a complete Lean proof of the central
Turing-completeness result of Stephen Dolan's 2013 paper, including the
four-register reduction. One fixed MOV body with an unconditional loop backedge
simulates every finite Turing machine and finite input, preserving halting and
divergence in the disclosed unbounded abstract machine model. Its stronger
stopping certificate reaches the deliberate invalid-zero-address MOV load
exactly when the source machine halts, following Dolan's Section 5.

Start with the [Dolan formalization guide](lean/DOLAN_FORMALIZATION.md).
The standalone result is
[`SmcTuring.Dolan.Four.four_register_mov_certified_simulation`](lean/SmcTuring/Dolan/FourStopping.lean).
The guide maps the paper's construction to the checked source and explains the
local source corrections, two-sided tape initialization and sentinel guard.
Dolan is explicitly credited as a formalized source in
[the metadata](lean/formalization.yaml). This result is proved independently of
the pure-SMC construction and is included in the same audited development.

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

### `MovTM` — MOV-based reference Turing machine

| Variant | Flag | Notes |
|---|---|---|
| Inline x86 | `1` | MSVC inline assembly; MOV computation with conventional loop/exit branches |
| External | `2` | MASM `MovTM`; x86 and x64; same data-based algorithm |
| C emulation | `4` | C translation of matching, tape movement, and state selection |

Symbol comparison uses indexed writes and reads into a scratch selector array.
The assembly also contains `cmp`, `je`, `jmp`, and `ret` for loop/exit control.
These are comparison implementations and are not the strict pure-SMC witness.

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

- **CMake 3.20 or later** and a C++11 compiler, targeting x86 or x86-64.
- **Windows:** Visual Studio 2022 or later with the MSVC C++ tools, MASM and Windows SDK.
- **Linux:** GCC or Clang, plus Make or Ninja. A 32-bit build also needs the
  multilib C++ runtime/development packages (for example, `g++-multilib` on Ubuntu).
- **Intel macOS (x86-64):** Apple Clang from the Xcode Command Line Tools and CMake.

Windows uses the original MASM routines in `tm.asm`. Linux and Intel macOS use
the System V ABI port in `tm.S`, with ELF/Mach-O declarations and Intel syntax.
MSVC's inline assembly
variants are enabled only for 32-bit MSVC builds.

## Building

Configure, build and run the tests:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --config Release --parallel 1
ctest --test-dir build -C Release --output-on-failure
```

With a Visual Studio generator, add `-A x64` to the configure command, or use a
separate build directory with `-A Win32`. Linux selects its native architecture; for a 32-bit
build use a separate directory and add `-DCMAKE_CXX_FLAGS=-m32 -DCMAKE_ASM_FLAGS=-m32`.
The `smcTuring` subdirectory can also be configured directly with `cmake -S smcTuring`.

On macOS, select `-DCMAKE_OSX_ARCHITECTURES=x86_64` to build the Intel backend.
The Linux/macOS executable is `build/smcTuring/smcTuring`; with a Visual Studio
generator it is `build/smcTuring/Release/smcTuring.exe`. It runs without a
keyboard pause. Use `--no-benchmark` for just the simulator results,
`--iterations 1000` to shorten benchmarking, or `--input 0111_0001_` to try another
equal-width binary addition whose result fits the first field. `--help` lists
the options. `cmake --install build --config Release --prefix <directory>` installs
the executable in `bin`.

CTest checks six addition inputs across every available simulator, a short
benchmark run and rejected invalid inputs. The CMake workflow builds and tests
Debug/Release on Windows x86/x64, Linux x86/x64 with GCC and Clang, and Intel macOS
with Apple Clang.
These comparison-program changes leave the registered Lean statement, proof
sources and published errata unchanged.
Comparison-only edits run the native build workflow; changes to the Lean or
native proof inputs retain the full proof and native-binding checks.

### Visual Studio convenience solution

CMake is the primary build. The checked-in `smcTuring.sln` also works with
Visual Studio 2022 and 2026, selecting v143/v145 from the hosting build tools.
Executables go to `build/msbuild/<toolset>/<platform>/<configuration>` and
intermediates to `build/msbuild/obj/<toolset>/<platform>/<configuration>`.
These directories are separate from CMake's generated projects and outputs.
CI checks all four solution configurations with each Visual Studio version
and verifies that builds do not recreate output folders in the source tree.

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
>   CMake preserves these requirements when the inline variants are enabled;
>   `-DSMCTURING_INLINE_ASM=OFF` builds only the C++ and external assembly variants.

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

The repository code is released under CC0 1.0; see [LICENSE.txt](LICENSE.txt).
The paper itself is published under a
[Creative Commons Attribution-NonCommercial 4.0 International](https://creativecommons.org/licenses/by-nc/4.0/)
licence.
