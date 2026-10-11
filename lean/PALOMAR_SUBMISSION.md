# Palomar submission packet

**Ready for replacement submission.** The candidate uses Lean
`4.35.0-rc3` and Mathlib `5e043698502894993991089b2dd893867c0db5c2`, with
its complete upstream dependency snapshot. The full
[unmodified renderer passes](https://github.com/GregoryMorse/smcTuring/actions/runs/38162124185).
The [cold proof audit](https://github.com/GregoryMorse/smcTuring/actions/runs/38162641959)
and [official mechanical preflight](https://github.com/GregoryMorse/smcTuring/actions/runs/38163151000)
both pass. No renderer patch is needed for this submission.

| Form field | Exact value |
| --- | --- |
| Repository | `GregoryMorse/smcTuring` |
| Commit | `a97fbd690b4051463a3b3fe86b5823823aa91bac` |
| Project directory | `lean` |
| Comparator configuration | `lean/comparator.json` |
| Formalization metadata | `lean/formalization.yaml` |
| Responsible author/maintainer | Gregory Morse |
| Authorization relationship | I am a responsible author or maintainer |
| Approval evidence | Blank for the responsible-maintainer route |
| Submission type | Replace the existing first submission |
| Existing Palomar ID | Blank — no registered result |
| Preliminary override | Disabled |

Gregory Morse's first submission used
`e6aaea4723a82ee50385ac4d7991fbde9ba8ae03`. It passed
[mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/38141132403).
No registration is claimed. Leave the existing Palomar ID blank when retrying.
The form's replacement choice after GitHub authentication closes the prior
submission and starts the corrected one in one transaction; a separate manual
withdrawal is unnecessary. See
[the server's replacement contract](https://github.com/PalomarRegistry/PalomarServer#the-state-a-submission-holds).

[The renderer compatibility note](PALOMAR_RENDER_COMPATIBILITY.md) and
[check receipt](acceptance/palomar-render-compatibility.json) record the
dependency alignment and separate optional
[upstream PR](https://github.com/PalomarRegistry/PalomarSubmission/pull/166).
The successful unmodified render used `720a682c9e9185992200efd2a7467b2438704348`;
the candidate's subsequent changes affect validation drivers only. Every
renderer input is identical between those commits.

The accepted statement surface selects four theorems:

```
PalomarSMC.mathematical_result
SmcTuring.Dolan.Encoding.zigzag_injective
SmcTuring.SMC.Concrete.data_owner
SmcTuring.SMC.Concrete.metadata_owner
```

and four definitions:

```
SmcTuring.CorrectedPaper.Unbounded
SmcTuring.CorrectedPaper.FourMov
SmcTuring.CorrectedPaper.EffectiveInterpreter
SmcTuring.CorrectedPaper.Observations
```

Suggested submission notes:

> Source-based formalization of Gregory Morse's IJET 2018 pure self-modifying-code
> construction, with minimal positively proved errata M01–M20 and a credited
> Stephen Dolan MOV foundation. The principal mathematical result uses an ideal
> unbounded integer-address machine. Conditional finite x86/x64 native and COFF
> proofs are included as supporting material, outside the selected registered
> claims. The original paper's mathematical authorship is retained; Codex made
> substantial proof/tooling contributions under the author's direction. No new
> theorem priority or independent human review is claimed.

[Official full preflight](https://github.com/GregoryMorse/smcTuring/actions/runs/38163151000): **pass**, pipeline revision
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, `palomar-standard-v1`.
The only warning concerns the preferred Challenge review surface; 984 physical
lines / 60,700 bytes remain within the 1,000-line hard limit. Lean, NanoDa and
con-ron accept the selected declarations. The detected and declared repository
license are both CC0-1.0; cited publications retain their own terms.

[Native acceptance](https://github.com/GregoryMorse/smcTuring/actions/runs/38118165923)
passes all 21 suites and four baseline configurations. Its source is unchanged.
The new [cold proof audit](https://github.com/GregoryMorse/smcTuring/actions/runs/38162641959)
passes with the aligned dependencies: 1,152 freshly compiled modules / 7,976
audited declarations, no module reuse and only standard axioms. The
[alignment receipt](acceptance/palomar-render-compatibility.json) records the
completed runs and report hashes. [Original final acceptance](FINAL_ACCEPTANCE.json)
retains the earlier proof and native evidence with their original source bindings.

The earlier cold proof acceptance source is
`1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4`. Project Lean source, native source
and errata are unchanged.
Palomar will verify the replacement commit itself. Prior run receipts remain
bound to their original sources. [Semantic account](PALOMAR_SEMANTICS.md),
[theorem map](FINAL_THEOREM_MAP.md), [physical contract](PHYSICAL_BINDING_CONTRACT.md),
[minimal diff](errata/morse-2018-minimal.diff), [TeX](errata/morse-2018-errata.tex)
and [reviewed PDF](../output/pdf/morse-2018-errata.pdf) accompany the source.

Classification: `cs.LO`; MSC `03D10`, `68N30`. Metadata identifies the source
relationships (`adapts` Morse, `formalizes` Dolan), background literature and
pinned Mathlib dependency. Mechanical readiness does not claim editorial acceptance.
