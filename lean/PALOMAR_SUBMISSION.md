# Palomar submission packet

**Revision required.** The latest review requires explicit computable witness
initialization and actual numbered-interpreter reachability for journal output.
The candidate below is historical. Use the new tested candidate only after
[the execution revision ledger](EXECUTION_REVISION_LEDGER.md) is complete.

The earlier semantic revision corrects the dependency account and strengthens both
MOV stopping and unbounded executed-field ownership. Use the candidate and
completed check bindings recorded in [SEMANTIC_REVISION_LEDGER.md](SEMANTIC_REVISION_LEDGER.md).
Earlier candidate `a97fbd690b4051463a3b3fe86b5823823aa91bac` is historical;
it does not contain these corrections. A new submission requires a newly
verified public commit. Intake remains Gregory Morse's action.

| Form field | Value |
| --- | --- |
| Repository | `GregoryMorse/smcTuring` |
| Commit | `16bd686e33c2ceff4bd3efe6c0d6e91f4e67ffc0` |
| Project directory | `lean` |
| Comparator configuration | `lean/comparator.json` |
| Formalization metadata | `lean/formalization.yaml` |
| Responsible author/maintainer | Gregory Morse |
| Authorization relationship | I am a responsible author or maintainer |
| Approval evidence | Blank for the responsible-maintainer route |
| Existing Palomar ID | Blank — this result has not been registered |
| Preliminary override | Disabled |

Lean remains `4.35.0-rc3`; Mathlib remains
`5e043698502894993991089b2dd893867c0db5c2` with its pinned upstream dependencies.
The original acceptance at `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4` used
Mathlib `302343bb9a029d4edab4f736703f0736896c1b64`. The
[alignment receipt](acceptance/palomar-render-compatibility.json) documents
the later dependency change and earlier successful unmodified rendering.
The optional [upstream renderer PR](https://github.com/PalomarRegistry/PalomarSubmission/pull/166)
is independent of this revision and is not required for submission.

The statement selects four theorems:

```text
PalomarSMC.mathematical_result
SmcTuring.Dolan.Encoding.zigzag_injective
SmcTuring.SMC.Concrete.data_owner
SmcTuring.SMC.Concrete.metadata_owner
```

and four definitions:

```text
SmcTuring.CorrectedPaper.Unbounded
SmcTuring.CorrectedPaper.FourMov
SmcTuring.CorrectedPaper.EffectiveInterpreter
SmcTuring.CorrectedPaper.Observations
```

[The definition-level alignment](SEMANTIC_ALIGNMENT.md) explains each claim,
its cited source, and the positive certificate. `Unbounded` now requires the
changed field's owning STORE to be fetched at the next instruction time.
`FourMov` now includes an explicit zero-address trapping load certificate as
well as halt/divergence equivalence and the fixed body length. Dolan's Section 5
uses that stopping convention; invalid reads do not return zero.

Suggested submission notes:

> Formalization of Gregory Morse's IJET 2018 pure self-modifying-code construction,
> with minimal positively proved errata M01–M20 and Stephen Dolan's credited MOV
> foundation. The ideal unbounded model includes a pure trace changing unboundedly
> many distinct operand fields whose owning instructions are immediately fetched.
> The static four-register MOV simulator has a positive certificate for the
> deliberate invalid-zero-address read exactly when the source TM halts.
> Conditional finite x86/x64 native and COFF proofs remain supporting material.
> Codex made substantial proof/tooling contributions under the author's direction.
> No new priority, independent human review or registry endorsement is claimed.

The [revision acceptance receipt](acceptance/semantic-revision.json) records
the passing full audit (1,154 fresh modules and 7,995 declarations), all 21
Windows native suites, protected unmodified Palomar preflight and unmodified
Challenge rendering for the exact commit above. The Challenge remains subject to the hard
1,000-line / 100 KiB limit. The preferred smaller-surface warning is disclosed.

The [21-suite native acceptance](https://github.com/GregoryMorse/smcTuring/actions/runs/38118165923)
and [original final acceptance](FINAL_ACCEPTANCE.json) retain their original
source bindings. Native C++/ASM and the published minimal errata are unchanged
by this semantic revision. Their existing evidence is supporting material;
it is not used to substitute for the new mathematical checks.

The repository formalization license is CC0-1.0. Cited publications retain
their source terms. No registration is claimed, and the private submission
access link is deliberately absent from tracked files.
