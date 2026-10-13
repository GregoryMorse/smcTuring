# Explicit initialization and reached interpreter output — complete

**All five revision obligations are COMPLETE.** Exact tested source:
`51198ac6ad1d1b4b2ad6e3751583e3c6d1c56b71`.
[Acceptance receipt](acceptance/execution-revision.json) records source/report bindings.

The 2026-10-12 review at 13:14:35Z identified two gaps in the selected
statement. Earlier successful kernel, native and renderer receipts certify
their historical statements. They do not certify this strengthening.

| Item | Required positive evidence | State |
| --- | --- | --- |
| E01 | Selected `Unbounded` names the literal fixed-register, identity-memory initializer and requires its memory function to be primitive recursive. | COMPLETE |
| E02 | Each terminal journal belongs to a halted configuration reached by the same numbered interpreter from the same encoded input. | COMPLETE |
| E03 | Independent Challenge contains the exact stronger definitions; Solution and umbrella theorem prove them. | COMPLETE |
| E04 | Audit every selected clause for explicit initialization, actual execution, output identity and model assumptions. | COMPLETE |
| E05 | Source-bound targeted proof checks, final full acceptance and unmodified Palomar verification/rendering. Publish the exact tested source. | COMPLETE |

The initializer is `acc = 39`, `stack = 0`, `pc = owner 40 - 1`,
`carry = false`, `memory field = field`. The selected witness is this state,
not an existential unrestricted function. `active_initial_memory_primrec`
and `computably_initialized_unbounded_smc_witness` expose the positive proof.

The output clause requires
`StateTransition.Reaches (TM0.step numbered) (TM0.init encodedInput) library`
and `TM0.step numbered library = none`. `JournalOutput` uses this same
`library.Tape.right₀`, with its source tape represented in the actual reached
SMC terminal state. These facts are obtained from the configuration evaluation
already derived by `standard_terminal_output`; they are not new hypotheses.

Check affected roots serially with source-bound reuse during iteration.
Do not recheck unchanged theorems between attempts. Keep the approved Lean
and Mathlib pins and all existing local/remote resource limits. A new
submission candidate is ready only after its own required checks pass.

| Final check | Passing evidence |
| --- | --- |
| Full proof/native CI | [38281964773](https://github.com/GregoryMorse/smcTuring/actions/runs/38281964773): 1,155 fresh modules, 7,997 declarations under standard axioms, 210 Windows exporter modules, all 21 native suites and 30 baseline checks |
| Protected Palomar verification | [38281992323](https://github.com/GregoryMorse/smcTuring/actions/runs/38281992323): exact four result definitions and four theorems accepted by the unmodified protected checks |
| Unmodified rendering | [38281996012](https://github.com/GregoryMorse/smcTuring/actions/runs/38281996012): exact stronger Challenge, 1,000 lines / 62,027 bytes |

Iteration used the affected 91-module closure, with source-bound reuse after
successful checkpoints. The final complete replay above ran once on the
frozen candidate. Reports and manifests have been fetched locally.
The new constraints are formalization statement corrections; the published
minimal paper errata and native C++/ASM source did not change.
Gregory Morse completed intake and registration as
[PALOMAR-2026-10-13-000008, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-13-000008&version=1).
The [registration receipt](acceptance/palomar-registration.json) confirms the
same tested source.
