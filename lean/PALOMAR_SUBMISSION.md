# Palomar submission packet

**Ready for Gregory Morse to submit.** The official full mechanical preflight
passes on the immutable source below. Submission/registration has not been performed.

| Form field | Exact value |
| --- | --- |
| Repository | `GregoryMorse/smcTuring` |
| Commit | `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4` |
| Project directory | `lean` |
| Comparator configuration | `lean/comparator.json` |
| Formalization metadata | `lean/formalization.yaml` |
| Responsible author/maintainer | Gregory Morse |
| Authorization relationship | I am a responsible author or maintainer |
| Approval evidence | Blank for the responsible-maintainer route |
| Existing Palomar ID | Leave blank for a first submission; supply the existing ID if previously registered |
| Preliminary override | Disabled |

The automatic identity lookup returned HTTP 403, which does not establish
whether an existing record exists. Choose the appropriate first-submission or
existing-record route. No false negative lookup is asserted.

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

[Official full preflight](https://github.com/GregoryMorse/smcTuring/actions/runs/38108849833): **pass**, pipeline revision
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

The repository's latest master adds CI/runtime fixes and closure documents.
Use the **exact commit above** for this accepted submission. All selected proof
and native algorithm source is identical. [Semantic account](PALOMAR_SEMANTICS.md),
[theorem map](FINAL_THEOREM_MAP.md), [physical contract](PHYSICAL_BINDING_CONTRACT.md),
[minimal diff](errata/morse-2018-minimal.diff), [TeX](errata/morse-2018-errata.tex)
and [reviewed PDF](../output/pdf/morse-2018-errata.pdf) accompany the source.

Classification: `cs.LO`; MSC `03D10`, `68N30`. Metadata identifies the source
relationships (`adapts` Morse, `formalizes` Dolan), background literature and
pinned Mathlib dependency. Mechanical readiness does not claim editorial acceptance.
