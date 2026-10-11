# Established TM alignment and converse certificate

## Current acceptance — 2026-10-11

Mathematical proofs and conditional native/head/COFF bindings are complete;
rounds 1–6 are accepted at immutable passing checkpoints. The final cold replay
checks 1,151 modules / 7,975 declarations with zero reuse. See
[the current closure status](CLOSURE_STATUS.md), [the final theorem map](FINAL_THEOREM_MAP.md)
and [the Palomar audit](PALOMAR_AUDIT.md). Actual public-commit/native CI and
Palomar acceptance remain open. The dated development descriptions below are
historical and do not reopen completed mathematical dependencies.


Date: 2026-10-04. T01 and T13 are checked in the stated word model.

The actual Mathlib TM0-to-source compiler and its composition with pure SMC are
checked in `MathlibTM0/Compiler.lean` and `MathlibTM0/Simulation.lean`. The reverse
source-to-TM0 adapter is checked in `MathlibTM0/Reverse.lean`, including arbitrary
blank/start values, exactly three labels per source state, two actual TM0 steps
per transition, halting equivalence and full relative tape output.
The finite-data evaluator has a checked TM computability certificate in G40-G56.
It covers the actual lookup/scalar algorithms and unbounded terminal search,
including literal finite labels, exact halting and complete journal output.

## Pinned dependency

The public Mathlib repository's `master` was resolved with `git ls-remote` to
`302343bb9a029d4edab4f736703f0736896c1b64`. Its
[pinned toolchain file](https://raw.githubusercontent.com/leanprover-community/mathlib4/302343bb9a029d4edab4f736703f0736896c1b64/lean-toolchain)
reports `leanprover/lean4:v4.35.0-rc3`, matching this project. The dependency is
installed and imported; all eight transitive revisions are locked in the
project's Lake manifest and match Mathlib's own pinned manifest.
`validation/mathlib.json` records metadata hashes and the selected TM0 cache;
`validation/lean.json` records project configuration and the imported transition,
tape, TM0, finite-label and primitive-recursion library source hashes, plus
the pinned Lean bitwise implementation alongside the kernel axiom audit.

The imported [pinned TM0 source](https://github.com/leanprover-community/mathlib4/blob/302343bb9a029d4edab4f736703f0736896c1b64/Mathlib/Computability/TuringMachine/PostTuringMachine.lean)
uses one write or one head move per step. The alphabet's default is its blank
symbol, the label default is the initial state, and a missing transition halts.
Its tape uses finite blank tails. These declarations were confirmed in the
installed pinned snapshot before proving the compiler.

## Adapter contracts

1. **Checked (G39).** Encode the finite source alphabet and labels with defaults corresponding to
   the supplied blank and start values. Relate every relative tape position to
   the source's absolute integer position and head; prove initialization and
   preservation of the entire tape, including both blank tails.
2. **Checked (G39).** Translate a source write/move transition into a write phase followed by a
   move phase. The intermediate label remembers only destination and direction.
   Prove two actual TM0 steps per successful source step, no halt in an
   intermediate phase, and finite support of the generated labels.
3. **Checked (G37).** Translate a TM0 move into one source step that writes the old symbol and
   moves. Translate a TM0 write into a source write/right step followed by a
   left step that rewrites the encountered neighbor with its existing symbol.
   Prove full tape restoration, positive bounded progress, and intended halting
   only at original labels. This direction connects established-library machines
   to the existing pure SMC compiler.
4. **Checked (G38-G39).** Compose the trace relations into halting/divergence and complete output
   correspondence. State the right-tail output convention separately from the
   project's full tape/head observation; preserve the stronger observation.

`compiler_respects` proves Mathlib's actual `StateTransition.Respects` contract.
`standard_halts_iff` uses its partial-evaluation domain theorem, and
`fixed_smc_mathlib_simulation` connects `Turing.TM0.eval` directly to the fixed
SMC image's terminal reachability, infinite execution, instruction purity and
arbitrarily late actual code changes. `standard_terminal_output` recovers a
genuine member of Mathlib's partial output and the complete relative tape from
the terminal code words. No adapter or simulation theorem is assumed.

`Reverse.labels_card` proves exactly three finite phases per source label.
`Reverse.two_steps` composes the actual library write and move transitions.
`Reverse.halts_iff` and `Reverse.terminal_output` select the supplied blank and
start defaults and certify actual library evaluation for arbitrary source
machines. The per-phase `compiler_respects` contracts connect finite traces and
terminal outcomes using Mathlib's transition-refinement theorems.

TM0's tape observation is relative to its current head. The trace relation must
carry the source's absolute head coordinate throughout execution. If the
library's final tape output must also encode that coordinate, use a preserved
origin marker and prove the extended alphabet encoding separately.

## Converse execution certificate

G34-G36 already supply finite transition-table data, an independent list-journal
evaluator, exact prefix/fault correspondence and injective natural-list state
encoding. For a prefix of n instructions the state encoding has 4+2n entries.
The default-word and header algorithms are fixed definitions with finite data
inputs.

G40-G46 now certify newest-write journal lookup with a finite fallback word,
journal updates/flattening, canonical integer coding, signed addition/subtraction/
comparison/borrow, two's-complement XOR/AND, raw state packing/parsing, all ten
instruction effects and operand resolution as primitive recursive. G46 also
certifies the actual constructed image's header lookup, using a fixed finite
reader/control table and arithmetic negative-PC storage templates. The semantic
contracts cover every integer PC, missing headers and exact next-PC coding.
No function-valued header input is used. These certificates agree with the
existing finite evaluator and serialized states.

G47 supplies primitive-codable finite machine, frozen-table, entry and word
representations. Finite transition functions use Mathlib's vector encoding.
G48 certifies the actual initial-word generator: finite linked-record/register/
metadata caches and the two-sided input/blank/link formulas agree with the
existing initializer for every signed address. G49 composes fetch, operand
resolution, both fallback reads and all effects, then proves the complete bounded
loop primitive recursive and exactly equivalent to the existing finite evaluator,
including missing-header faults. No function-valued memory input occurs.

G50 now proves terminal prefix search partial recursive, with exact source
halting/divergence and complete terminal-journal recovery. G51 derives its
natural/vector certificates and actual finite `ToPartrec.Code` using
`Turing.ToPartrec.Code.exists_code`. G52 composes actual TM2 evaluation and
checks finite alphabet, optional-symbol local storage, four stacks, closed finite
control support, positive code-step simulation and initial progress. G53 composes
the actual TM2-to-TM1-to-TM0 reductions: finite alphabet and control support,
exact halting domain and recovery of the complete journal on the output's main
track. All these modules are imported, compiled and audited at the project pin;
their primary partial-recursion/compiler/reduction sources are hashed.

G54 (`MathlibTM0/FiniteSupport`) now restricts TM0 labels to the subtype
belonging to its finite support. `labels_card` counts exactly those labels;
`labelInhabited` retains the original start. `step_embedding` includes both
successful steps and a halt; `restrict_respects` supplies one actual step of
positive progress. `configuration_eval` preserves the complete two-sided tape,
and `eval_eq` preserves exact partial output.

G55 (`MathlibTM0/Numbering`) transports finite alphabets/labels to numbered
indices, explicitly retaining the supplied blank and start. The actual library
machine mapping supplies positive transition refinement. Both full configuration
evaluation and right-tail partial output commute with the encoding.

G56 (`SMC/ComputableFiniteTM0`) selects `Fintype.equivFin` for the restricted
labels and finite multi-track alphabet. `terminal_search_numbered_tm0` gives
one literal finite-label transition table and an explicit finite descriptor/tape
codec, with exact halting and full journal output for every input.
`terminal_search_pure_smc` composes the checked finite-label TM0/source/SMC
adapters, retaining divergence, per-instruction purity, arbitrarily late actual
changes on divergence, and complete terminal-journal/tape recovery. This closes
T13. The numbered table is chosen before the runtime input; the initializer
contains no information about future execution.

The audit tracks these public declarations and the pinned finite-numbering
source alongside the partial-recursion/compiler sources. The remaining main
work is byte/CPU refinement and source/outcome alignment; appendix and ancillary
claims remain separate full-scope gates.

Do not use an unrestricted transition callback, arbitrary initial-memory
function, or unbounded internal-variable type as a computation oracle in that
certificate. The checked concrete evaluator takes only finite table/input data.
Native byte/CPU refinement, appendix algorithms and the remaining source gates
remain separate requirements in the main ledger.
