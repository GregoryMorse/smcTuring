# Palomar submission audit — mechanical readiness passed

Audit date: 2026-10-11. **Ready for user submission.** Exact source commit:
`1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4`. The previously published mathematical result is formalized with
minimal positively proved corrections. No intake or registration has been performed.

| Gate | Result | Evidence |
| --- | --- | --- |
| Public immutable source and pinned dependencies | PASS | Public commit above; Lean 4.35.0-rc3 / `470d5ce1400764999581fd26d5d72b00d990b0f4`, pinned Mathlib |
| Complete proof/standard-axiom audit | PASS | 1,152 fresh modules, 7,976 declarations, zero reuse |
| Selected statement and exact comparison | PASS | Four theorems/four definitions; official protected kernels accept |
| Official full preflight | PASS | [Actual report](https://github.com/GregoryMorse/smcTuring/actions/runs/38108849833); status `pass`, no errors |
| License | PASS | Declared/detected CC0-1.0 match; [license account](LICENSE_AUDIT.md) |
| Metadata, taxonomy, provenance and source rules | PASS | Official preflight; known source-based formalization with disclosed AI role |
| Minimal errata | PASS | M01–M20, 60 exact excerpts, 128 positive proof references, reviewed two-page PDF |
| Windows native supporting evidence | PASS | [Actual acceptance](https://github.com/GregoryMorse/smcTuring/actions/runs/38118165923); 21 suites, four baseline configurations |
| Semantic fidelity and model boundaries | CHECKED | [Individual semantic accounts](PALOMAR_SEMANTICS.md), [theorem map](FINAL_THEOREM_MAP.md), [physical contract](PHYSICAL_BINDING_CONTRACT.md) |

The preferred Challenge size warning remains disclosed: 984 lines / 60,700 bytes
exceeds the preferred 300-line / 32 KiB surface, while satisfying the 1,000-line
hard limit. The official full verifier accepts it. The selected record is the
principal mathematical result; native/COFF proofs remain supporting material.
No new priority, independent human peer review or Palomar endorsement is claimed.

[FINAL_ACCEPTANCE.json](FINAL_ACCEPTANCE.json) provides exact run/source/report
digests. [The retained mechanical report](acceptance/palomar-mechanical-report.json)
is the actual official output. [The submission packet](PALOMAR_SUBMISSION.md)
provides concrete form values and the confirmed first-submission route. The user will
perform intake; editorial registration is a later registry decision.

Earlier policy/source review, eligibility discussion and interrupted-run recovery
details are preserved in [the dated audit](history/PALOMAR_AUDIT.before-public-closure-20261011.md). Its old
pending gates have been resolved by the actual results above. Policy revision
`96b034cc31a72a63d4f4041911dce337a85c9a04` and full-verifier revision
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` are recorded in the earlier audit and receipt.
