# Palomar submission packet

**Normal dependency alignment is being evaluated; no replacement submitted.** The original
submission passed mechanical verification. The project dependency override was
reverted. A narrow renderer patch now passes the complete HTML path with the
original proof and dependency pins; see the
[successful advisory run](https://github.com/GregoryMorse/smcTuring/actions/runs/38154282274).
The table records the existing submission. A compatible official Mathlib
snapshot also passes the unmodified renderer's merger, so an upstream PR is
not a necessary prerequisite if that snapshot passes fresh proof/render checks.
The current Mathlib pin is retained pending approval to change it.

| Form field | Exact value |
| --- | --- |
| Repository | `GregoryMorse/smcTuring` |
| Commit | `e6aaea4723a82ee50385ac4d7991fbde9ba8ae03` |
| Project directory | `lean` |
| Comparator configuration | `lean/comparator.json` |
| Formalization metadata | `lean/formalization.yaml` |
| Responsible author/maintainer | Gregory Morse |
| Authorization relationship | I am a responsible author or maintainer |
| Approval evidence | Blank for the responsible-maintainer route |
| Submission type | Existing first submission; replacement on hold |
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
[check receipt](acceptance/palomar-render-compatibility.json) explain
the tested and reverted dependency change. The
[complete renderer probe](https://github.com/GregoryMorse/smcTuring/actions/runs/38152118403)
failed during Mathlib cache discovery. It is advisory, not a Palomar registration
or a new mechanical-verification receipt. Verso's revision requirement conflicts
with this Mathlib snapshot's cache manifest check; a coherent dependency
snapshot is an ordinary alternative to the upstream renderer repair.
The [proposed renderer patch](../validation/ci/palomar-renderer-plausible.patch)
retains the submitted Mathlib-compatible pin and accepts only the known
source-identical Plausible pair. Its complete test passes all eight selected
declaration surfaces and produces the sanitized HTML bundle, with no changes
to the accepted Lean source, cache checks or sandbox policy.

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

[Original-source official full preflight](https://github.com/GregoryMorse/smcTuring/actions/runs/38108849833): **pass**, pipeline revision
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, `palomar-standard-v1`.
The only warning concerns the preferred Challenge review surface; 984 physical
lines / 60,700 bytes remain within the 1,000-line hard limit. Lean, NanoDa and
con-ron accept the selected declarations. The detected and declared repository
license are both CC0-1.0; cited publications retain their own terms.

[Native acceptance](https://github.com/GregoryMorse/smcTuring/actions/runs/38118165923) passes all 21 suites and four baseline configurations.
The [complete cold proof audit](https://github.com/GregoryMorse/smcTuring/actions/runs/38108181056) checks 1,152 modules / 7,976 declarations,
with only standard axioms. The later packaging failure was repaired without
repeating the audit. [Final acceptance](FINAL_ACCEPTANCE.json) binds the recovered
source/driver distinction, actual run URLs and report hashes.

The earlier cold proof acceptance source is
`1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4`. Dependency configuration has been
restored after the unsuccessful renderer workaround. All selected proof and
native algorithm source is identical. Once the renderer compatibility issue is
resolved by verified dependency alignment or compatible deployed rendering,
record the exact replacement commit here.
Palomar will verify that newly submitted commit; prior run receipts remain bound
to their original sources. [Semantic account](PALOMAR_SEMANTICS.md),
[theorem map](FINAL_THEOREM_MAP.md), [physical contract](PHYSICAL_BINDING_CONTRACT.md),
[minimal diff](errata/morse-2018-minimal.diff), [TeX](errata/morse-2018-errata.tex)
and [reviewed PDF](../output/pdf/morse-2018-errata.pdf) accompany the source.

Classification: `cs.LO`; MSC `03D10`, `68N30`. Metadata identifies the source
relationships (`adapts` Morse, `formalizes` Dolan), background literature and
pinned Mathlib dependency. Mechanical readiness does not claim editorial acceptance.
