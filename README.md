# smcTuring — Pure Infinitely Self-Modifying Code Turing Machine


**Current verification policy (2026-10-11):** Lean is pinned to
`leanprover/lean4:v4.35.0-rc3`, commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`.
Run every build/test command serially through `validation/limited_run.py`.
Windows caps aggregate committed allocation at 1.5 GB; a 25 ms monitor also
stops the job at a conservative 1.5 GB resident threshold. Direct Lean uses
`-M768 -j1`. Never retry a capped failure without the guard.
The final cold Linux replay passes 1,151 production modules and 7,975 declarations
with zero project-cache reuse and only standard axioms. Mathematical proofs and
conditional native bindings are complete. Actual final public-commit CI and
Palomar acceptance remain open; see [the Palomar audit](lean/PALOMAR_AUDIT.md).
The selected Palomar interface now passes protected Comparator, NanoDa and
Lean's kernel. Its current source-bound audit checks 1,152 modules and 7,976
declarations, compiling only the new wrapper and reusing the 1,151 core modules.
See [current closure status](lean/CLOSURE_STATUS.md).


[![DOI](https://img.shields.io/badge/DOI-10.24425%2F119359-blue)](https://doi.org/10.24425/119359)
[![IJET](https://img.shields.io/badge/Journal-IJET_Vol._64_No._2_%282018%29-green)](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359)
[![Code license: CC0 1.0](https://img.shields.io/badge/Code_license-CC0_1.0-lightgrey.svg)](LICENSE.txt)

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

See the [proof ledger](lean/PROOF_LEDGER.md), [errata record](lean/ERRATA.md), and
[validation instructions](validation/README.md). The unbounded word-model
universality theorem and MOV foundation are kernel-checked. The constructed bounded
byte kernel and backedge now have checked fixed-allocation, canonical-address and
effective permission contracts. The full corrected-paper theorem and same-trace
appendix/native/COFF refinements are checked under the present-object and local
ISA conditions in [the physical contract](lean/PHYSICAL_BINDING_CONTRACT.md).
Actual source-bound release CI and Palomar verification remain separate gates.

The MOV foundation uses three addressing forms:

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

### `MovTM` ? MOV-based reference Turing machine

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

The repository code is released under CC0 1.0; see [LICENSE.txt](LICENSE.txt).
The paper itself is published under a
[Creative Commons Attribution-NonCommercial 4.0 International](https://creativecommons.org/licenses/by-nc/4.0/)
licence.

G93 checks the 33-instruction pointer construction: the base and offset are read from represented source registers, added in the single active load/store operand, then copied through the PointerWord reader into Candidate. Source-register aliases are allowed; all represented data and other owned metadata are preserved. G94 composes both guards and this pointer stage from original-memory setup. A malformed offset stops after 100 instructions; a valid offset reaches the Base guard after 222. The continuation is chosen exactly when the literal source address succeeds, and its selected heap word is left in the shared operand. Current-byte traces, code-owned writes, frames for other owned words outside the seven written fields, source-data preservation and reusable image/StackTop/SP/CF are checked. Remaining emitted role/compiler instantiation, applied bounds and hardware region/fetch refinement remain open.

G95-G96 check the complete native source load and store blocks. Both derive later reader/store setup from the executed guarded address stage and original static placement. The computed pointer is the single active operand shared by load and store. A successful load performs the literal source register update while preserving every other register and heap word; a successful store updates precisely the selected heap word and preserves all registers and other represented heap words. Source register names may alias. Malformed offsets stop after 100 instructions, malformed bases after 222, successful loads after 233 and stores after 239. Exact source outcomes, complete represented-state effects, current-byte traces, code-owned writes, owned-word frames and reusable image/StackTop/SP/CF are checked under explicit cell/no-wrap bounds. N18-N22 close whole emitted role/compiler instantiation under explicit capacity/compactness and source-path bounds. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

Validation uses lakefile.proof.toml with .lake/proof-build, separate from the editor cache. validation/lean_build.py checks that this Lake configuration differs from the canonical lakefile.toml only in buildDir; the package, Lean options, targets and dependency pins are identical. All Lean/native/encoding launchers use that configuration, and both configurations plus the shared launcher and proof audit script are hashed in the evidence. This avoids replacing editor-mapped Windows .olean.private files.

G97-G99 check native program composition, the actual backedge, and lowering of the exact exported 64-MOV kernel. Block readiness is derived from one initial metadata snapshot, physical field separation, the intact image and the actual selected heap pointer; no later trace or Ready is assumed. Finite schedules stop at the literal source trap and preserve all represented source data and code ownership. Successful schedules reach the computed end PC with a reusable invariant; the reset/indirect CALL composes into a closed pass. The kernel layout pass preserves all 64 instruction operands, a common source grid and contiguous encoded PCs. Its address-immediate rejection is explicit: the fixed kernel uses only offset immediates. N18-N22 now derive the complete static placement/metadata certificate from the padded emitter image and prove its full bounded/closed byte pass. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N00-N01 construct the literal inline packet sequences for all source blocks and both shared guards. The exact exported kernel has 1,678 source-body packets, and each guard has 37 inline packets. Physical source/guard positions, finer reader-caller/scalar-entry placement and whole-body embeddings in the padded image are derived from the packet builders. For compiled source schedules, explicit static end-position bounds discharge the conversion from encoded continuations to natural byte positions. N02-N08 now construct that aligned prefix, resolve its addresses and initialize all roles in the complete emitted byte image. N09-N17 derive context consistency, initial reader/scalar readiness, both complete guard certificates, the initial loop invariant and backedge setup. N18-N22 derive every compiled source block's initial Ready, immutable-role frames and the full source-schedule certificate. N23-N27 now construct finite loaded-prefix equivalence. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N02-N08 add 50 checked declarations for aligned templates and finite pools, literal role initialization, native byte lengths, affine metadata separation, the two-pass address allocator and complete byte-image initialization. The exact kernel occupies 9,382 bytes in x86 and 10,816 in x64; guards occupy 206 and 244 bytes. The constructed image contains all 23 shared readers, both guards, source body, backedge and 13 metadata owners; the host observation gap remains unfetched backing bytes. All reader and metadata operands have computed initial values, ownership and alignment, and represented source words initialize correctly in the protected data grid. N09-N17 prove that the source reference context equals this constructed whole and derive the guard and backedge certificates. N18-N22 derive every source block's initial Ready and the full source-schedule Setup. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. `ExportLayout.lean` supplies the allocator's coordinates for an independent finite MASM comparison; that comparison is evidence, not a proof of the Python generator or hardware semantics.


N09-N17 add 76 checked declarations. The fixed compilation now constructs a self-consistent complete byte image; all 23 reader and 13 metadata fit conditions follow from one finite source-grid capacity bound. Metadata fields, reader operands and both guard captures have injective physical and encoded addresses. Literal placed bytes and initialized operands derive reader/scalar/read-update readiness, both complete guard orientations, the initial represented/intact/frame/selected invariant and backedge Setup. Fixed control/register relocations use the explicit compactness condition `heapBase - origin < 2^31`; heap MOFFS operands use full-width capacity bounds. N18-N22 derive its frames across every compiled source block and each block's initial Ready, closing every field of `ProgramImage.Setup`. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. Overall completion remains incomplete.


N18-N22 add 38 checked declarations and close the whole emitted source-schedule certificate. Each block has an actual lowerer witness; its static observations belong to the constructed immutable role set, and that set is disjoint from its complete final-write destinations. All immediate/load/store initial Ready predicates follow from literal placed packets and initialized bytes, with source-register aliasing permitted. `ProgramCertificate.source_setup` supplies every field of `ProgramImage.Setup`; exact entry/end/Linked PCs and a full current-byte/code-owned bounded kernel pass are proved. `closed_pass_correct` composes an accepted pass with the actual backedge and restores the full invariant at kernel entry. Capacity, `heapBase - origin < 2^31`, positive cells and the path's source-address bounds remain explicit. N23-N27 construct finite loaded execution. N43-N55 close the allocation extent bounds. Physical mapping/canonical conditions, coherent hardware fetch, remaining source/appendix proofs and registry packaging remain open. Overall completion remains incomplete.

N23-N27 add 44 checked declarations for finite loaded-memory refinement. A finite byte image stores exactly the loaded interval; its partial evaluator automatically fetches current bytes and accepts only contained header/packet, data-read and full-word-write windows. Loaded-byte agreement preserves all selected scalar effects, write addresses/values, traces and ownership while framing exterior bytes. A computed containing interval supplies safety for every finite fetched prefix without assuming a safe execution. The whole emitted kernel and accepted body plus actual CALL backedge now have constructed finite loaded executions with literal source outcomes and every represented register/heap word preserved. The extent includes the complete represented finite grid. N43-N55 close containment in the prescribed allocation. Physical mapping/canonical conditions, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N28-N35 add 38 checked declarations for bounds in one allocation fixed by the emitted layout and requested finite source grid. Every placed control entry has a contained fifteen-byte fetch window; complete metadata, register, selected heap and all 23 initial reader-pointer words are contained, and the allocation fits the finite machine address space. Initial pointer/StackTop values and actual executed-state frames derive bounds for the repaired reader, reset/CALL, seven-instruction callee, ten-instruction caller round trip, each scalar operation and eleven-instruction read/update. Literal initialized placed callers and read/update fragments therefore have finite loaded executions in this prescribed allocation. N36-N42 compose the guards; N43-N55 complete the dynamic source and whole-kernel allocation certificate. Canonical-address validity, permissions/segmentation/CET, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N36-N42 add 22 checked declarations composing the fixed-allocation bounds through all guard stages. Static packet placement derives reader/callee/scalar/CALL fetch windows from one control interval. Proved pointer frames derive every data-read and complete word-write bound through the 26-instruction capture/setup, 13-instruction borrow-mask and 47-instruction selector/return stages. Both 86-instruction guard orientations and the actual 89-instruction outer invocation have finite loaded executions in the preselected allocation, derived from the initialized emitter image, capacity/compactness and typed metadata; no future safe trace or intermediate Ready is supplied. N35 additionally proves containment of the whole static control interval, bringing its declaration count to 19. N43-N55 close the remaining dynamic source and whole-kernel allocation bounds. Physical canonical/permission/segment/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.

N43-N55 add 31 checked declarations closing dynamic source and whole-kernel bounds in the allocation fixed before execution. Pointer construction reads contained register and operand words without dereferencing an unvalidated value. Successful load/store operands are proved equal to the selected contained heap word from source representation and finite-cell bounds; rejected tag paths execute their contained guards. All actual compiled blocks obtain static certificates from their literal lowerer witnesses. Schedule induction derives current Ready from the preserved invariant at every boundary, then composes the complete emitted body and actual reset/indirect CALL backedge. `ProgramAllocation.kernel_loaded` and `closed_loaded` construct their finite loaded executions with exact source outcomes, every represented register/heap word, code-owned writes and the closed entry PC. No future safe trace, intermediate Ready or trace-dependent allocation extent is supplied. Address-space capacity, compact relocations, positive cells and source-path cell bounds remain explicit. Physical mapping, canonical/segment/permission/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.

E20-E24 add 56 checked declarations closing the complete reference x86 branch.
One initialized byte image supplies every actual fetch through the predicate,
stack exchange/CALL and selected five-step continuation. Its actual target and
both end PCs are derived; EAX/ESP restored, CF=false, every reached DWORD write
code-owned, all protected packets intact and every original byte outside the
three final scratch fields restored. CALL's temporary DEFSTACK address word is
included. Only initial image, entry and finite extent are execution premises.
The endpoints are finite observation boundaries, not source halt. General native
host spacing and physical ISA/fetch/other architectural state remain separate.
See [APPENDIX_BYTE_IMAGE.md](lean/APPENDIX_BYTE_IMAGE.md).

E25-E30 add 72 checked declarations for independently spaced, ordered forward
x86 branch blocks. One original byte image supplies all pure fetches; the actual
Taken-Fall displacement, both continuation end PCs, EAX/ESP/CF restoration,
every owned DWORD write and exact host-gap backing bytes are derived. The native
comparator now checks all 338 complete pure packets at the actual twelve COFF
layouts, including target constants, destinations/owner coordinates and end PCs.
Only absolute payloads are normalized, with separate symbol/addend/relocation
checks. The actual host gaps are 50/12/76 bytes. Other region orderings/backward
geometry and physical ISA/configuration/coherent fetch remain separate.
See [APPENDIX_BYTE_SPACING.md](lean/APPENDIX_BYTE_SPACING.md).

The compact [publishable LaTeX errata](lean/errata/morse-2018-errata.tex) now records the exact M01-M11
local corrections and positive proof justifications. Its location-annotated diff
is checked against 33 published excerpts; `python validation/limited_run.py -- python validation/audit_errata.py`
checks all 70 positive proof references and the two-page PDF. These corrections
are separate from continuing full-paper and physical ISA refinement obligations.

Listing 11 now has 329 checked multiplication declarations: modular arithmetic,
literal data-block effects, actual patched-displacement loop dispatch, all-input
product/termination, input/accumulator restoration, whole-data-trace purity and
exterior-word framing. Its minimally corrected literal x86 fixture passes
11,458 cases. E34-E36 complete selected word/register CALL/ESP and actual-PC loop composition. E37-E40 add the exact missing byte forms, finite-field refinement and all 55 literal packets plus four inactive owners. Native comparison checks all 422 bytes, fourteen fields and 57 address relocations. E41-E45 construct the original image, derive all fourteen code owners and build actual current-byte traces/invariant/refinement for each data block. E46-E49 derive original operands/stack/CALL setup and complete live-byte blocks, including arithmetic-derived control targets/endpoint PCs, owned writes and finite field refinement. E50-E52 close the entire original-image actual-PC/current-byte loop, product, registers/inputs, owned writes and exact original exterior-byte frame outside ten scratch/result fields. E03 is checked for the selected byte machine; physical ISA/configuration/fetch remains E05.
See [the multiplication scope](lean/APPENDIX_MULTIPLICATION.md).

The complete audit has **3,496** declarations and **370** unique ledger IDs.
E121-E131 add **170** positive byte-layout/execution declarations, and E116
adds the common-byte run bridge. E132 checks that the constructed original
image, its actual owner fields and six placement premises match all four
native layouts.

`DivisionByteCorrect.correct` now constructs the entire continuous current-byte
execution from one original emitted image, entry PC, static ordered placement/
capacity bounds and nonzero inputs. It proves all four quotient/remainder
results, exact CF, input/EAX/ESP restoration, endpoint PC, zero displacement,
only code-owned DWORD writes and every original byte outside the actual
scratch/result fields. `reusable_correct` derives another complete invocation
from the maintained image/stack/reset and current inputs with arbitrary scratch
values. Signed quotient truncates toward zero, excluding MIN_INT/-1 only for
an in-range integer quotient; the remainder theorem includes that case.

Native regression passes **52,648** executions. All **344** unique packets,
**2,532** complete bytes, **333** DIR32 sites and **91** mode-owned fields match
actual Lean, including the constructed whole original image. E04 is checked
for the selected finite x86 byte machine. Physical ISA/configuration/coherent
fetch, remaining literal source/x64 placements and
review-package gates retain their full scope. M01-M11, 33 exact excerpts,
70 positive errata references and the compact two-page TeX/PDF are unchanged.

See [the division proof scope](lean/APPENDIX_DIVISION.md).

The complete branch theorem now also permits all disjoint region orders and
backward targets (E133-E134). Ten static checks derive the entire current-byte
trace, actual target/endpoint, input/EAX/ESP/CF, owned writes and original-byte/
gap frame. E135 passes all 24 orders/288 layouts/144 backward targets/1,785,600 native
executions, with 8,112 full packets/2,016 owner fields/8,112 DIR32 sites matching
Lean;
see [the branch geometry record](lean/APPENDIX_BYTE_SPACING.md). The audit has 3,496 declarations and
370 ledger IDs. Remaining literal source/x64 placement, physical ISA/fetch and
review-package gates retain their scope; the compact errata is unchanged.
