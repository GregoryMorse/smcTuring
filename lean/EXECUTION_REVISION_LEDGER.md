# Explicit initialization and reached interpreter output

The 2026-10-12 review at 13:14:35Z identified two gaps in the selected
statement. Earlier successful kernel, native and renderer receipts certify
their historical statements. They do not certify this strengthening.

| Item | Required positive evidence | State |
| --- | --- | --- |
| E01 | Selected `Unbounded` names the literal fixed-register, identity-memory initializer and requires its memory function to be primitive recursive. | TARGETED LEAN PASS |
| E02 | Each terminal journal belongs to a halted configuration reached by the same numbered interpreter from the same encoded input. | TARGETED LEAN PASS |
| E03 | Independent Challenge contains the exact stronger definitions; Solution and umbrella theorem prove them. | IMPLEMENTED; protected comparison pending |
| E04 | Audit every selected clause for explicit initialization, actual execution, output identity and model assumptions. | COMPLETE; definition-level alignment audited |
| E05 | Source-bound targeted proof checks, final full acceptance and unmodified Palomar verification/rendering. Publish the exact tested source. | PENDING |

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
