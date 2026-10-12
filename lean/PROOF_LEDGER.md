# Proof ledger — original closure and semantic revision

**Full corrected-paper formalization and release validation complete, 2026-10-11.**
This historical acceptance applies to the original definitions. The 2026-10-12
strengthening and its completed release checks are recorded in
[SEMANTIC_REVISION_LEDGER.md](SEMANTIC_REVISION_LEDGER.md). The complete development ledger, including its original IDs, dependency
tables and dated intermediate states, is preserved in
[the historical ledger](history/PROOF_LEDGER.before-public-closure-20261011.md). Historical
`IN_PROGRESS` entries describe those dates; they are not current obligations.

| Obligation | State | Positive evidence |
| --- | --- | --- |
| Original source baseline | CHECKED | Four configurations and 30 simulator checks in final native CI |
| Corrected DEFADDR boundary equivalence and purity | CHECKED | `SmcTuring.Defaddr`; original/corrected x86/x64 tests |
| Stephen Dolan MOV foundation | CHECKED | `Dolan.Four.four_register_mov_certified_simulation` |
| Pure SMC simulation, halt/divergence and unbounded changed fields | CHECKED | `CorrectedPaper.full_paper` |
| Effective interpreter and tape/head observations | CHECKED | `CorrectedPaper.observations`, effective terminal construction |
| Complete printed Listing 8/9 same-prefix executable/owner invariant | CHECKED | `Listing9JointFullExecution.complete_input` |
| Native trace, output/head and exact AX restoration boundary | CHECKED | `Listing9SameTraceBinding.complete_input` |
| Conditional normalized-object/COFF physical binding | CHECKED | `Listing9PhysicalBinding.full_paper` |
| M01–M20 minimal corrections | CHECKED | Exact diff, TeX, edit manifest and reviewed PDF |
| R01: independent selected Challenge/Solution | CHECKED | Four theorem names and four definition names |
| R02: protected Comparator and independent kernels | CHECKED | Official full Palomar report: pass |
| R03: provenance, metadata and license | CHECKED | Schema/taxonomies and matching detected CC0-1.0 |
| R04: immutable public snapshot and release evidence | CHECKED | `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4`; complete source-bound Linux/Windows CI |

[FINAL_THEOREM_MAP.md](FINAL_THEOREM_MAP.md) maps the precise theorem families.
[FINAL_ACCEPTANCE.json](FINAL_ACCEPTANCE.json) binds the fresh 1,152-module /
7,976-declaration audit, 21 native suites and Palomar workflow to the public
source. [CLOSURE_ROUNDS.json](CLOSURE_ROUNDS.json) closes all seven rounds.
Only `propext`, `Quot.sound` and `Classical.choice` occur; Solution/development
has zero holes. The four intentional Challenge theorem holes are the statement
interface accepted by Comparator.

The unbounded result uses the ideal integer-address model. Native/physical
claims retain explicit finite capacity/reach and local ISA/mapping/ABI conditions,
with head observed before cleanup and exact epilogue/trailing-x64 AX effects.
Palomar intake and editorial review are user/registry actions outside this closed
proof ledger. No registration or independent human review is claimed.
