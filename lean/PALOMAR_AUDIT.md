# Palomar submission audit

**Registered:** [PALOMAR-2026-10-13-000008, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-13-000008&version=1),
published 2026-10-13. The [registration receipt](acceptance/palomar-registration.json)
binds the public record to the exact tested source:
`51198ac6ad1d1b4b2ad6e3751583e3c6d1c56b71`.
The [acceptance receipt](acceptance/execution-revision.json) records source and
report hashes; the [submission packet](PALOMAR_SUBMISSION.md) gives the form values.
The [definition-level alignment](SEMANTIC_ALIGNMENT.md) and
[closed execution revision ledger](EXECUTION_REVISION_LEDGER.md) cover both
requested stronger corrections. Earlier receipts retain their historical bindings.

| Gate | Result | Evidence |
| --- | --- | --- |
| Public immutable source and pinned dependencies | PASS | Public commit above; Lean 4.35.0-rc3 / `470d5ce1400764999581fd26d5d72b00d990b0f4`, pinned Mathlib |
| Complete proof/standard-axiom audit | PASS | [Full CI](https://github.com/GregoryMorse/smcTuring/actions/runs/38281964773): 1,155 fresh modules, 7,997 declarations, zero reuse |
| Selected statement and exact comparison | PASS | Four theorems/four definitions; official protected kernels accept |
| Official full preflight | PASS | [Actual report](https://github.com/GregoryMorse/smcTuring/actions/runs/38281992323); status `pass`, no errors; Lean/Nanoda/con-ron checks |
| Unmodified Challenge rendering | PASS | [38281996012](https://github.com/GregoryMorse/smcTuring/actions/runs/38281996012): matching source and Challenge hash |
| License | PASS | Declared/detected CC0-1.0 match; [license account](LICENSE_AUDIT.md) |
| Metadata, taxonomy, provenance and source rules | PASS | Official preflight; known source-based formalization with disclosed AI role |
| Minimal errata | PASS | M01–M20, 60 exact excerpts, 128 positive proof references, reviewed two-page PDF |
| Windows native supporting evidence | PASS | Full CI above: 210 exporter modules, 23 roots, 21 suites and 30 checks in four baseline configurations |
| Earlier semantic account | SUPERSEDED | Current [definition-level audit](SEMANTIC_ALIGNMENT.md) explicitly distinguishes trapping zero-address reads and executed owners from dormant template placement. |

The preferred Challenge size warning remains disclosed: 1,000 lines / 62,027 bytes
exceeds the preferred 300-line / 32 KiB surface, while satisfying the 1,000-line
hard limit. The official full verifier accepts it. The selected record is the
principal mathematical result; native/COFF proofs remain supporting material.
No new priority, independent human peer review or Palomar endorsement is claimed.

`Unbounded` names the literal fixed-register, identity-memory initializer and
requires its primitive recursiveness. `EffectiveInterpreter` requires its
journal-bearing halted configuration to be reached by the same numbered
machine on the encoded input. The earlier executed-owner and deliberate
invalid-zero-load corrections remain in force.

The supplied submission auditor found no static errors and one preferred-size
warning. Its mandatory mechanical items are resolved by the protected full
report; the statement audit is recorded separately in the alignment above.
Live policy and intake guidance were refreshed on 2026-10-12. All reports,
logs and manifests have been fetched locally. No progressed proof work remains
only on the server. Gregory Morse completed replacement intake and registration.
The public record reports trust level `high`; it is not an independent human review.

Earlier policy/source review, eligibility discussion and interrupted-run recovery
details are preserved in [the dated audit](history/PALOMAR_AUDIT.before-public-closure-20261011.md). Its old
pending gates have been resolved by the actual results above. Policy revision
`96b034cc31a72a63d4f4041911dce337a85c9a04` and full-verifier revision
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` are recorded in the earlier audit and receipt.
