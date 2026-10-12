# Lean formalization of pure infinitely self-modifying code

This development formalizes the corrected mathematical construction and its
conditional native realization. [Selected semantics](PALOMAR_SEMANTICS.md)
defines the registry scope. [The submission packet](PALOMAR_SUBMISSION.md)
binds each acceptance result to its tested commit; the current semantic revision
has historical [source-bound acceptance](acceptance/semantic-revision.json).
The new explicit-initialization and reached-output strengthening is tracked in
[its ledger](EXECUTION_REVISION_LEDGER.md).
Mechanical verification and statement-to-source agreement are distinct checks.

Gregory Morse's [2018 paper](https://doi.org/10.24425/119359) is the mathematical
source. The [minimal errata TeX](errata/morse-2018-errata.tex),
[exact excerpt diff](errata/morse-2018-minimal.diff) and
[two-page PDF](../output/pdf/morse-2018-errata.pdf) preserve the published
construction with M01-M20 local corrections and model clarifications.
The original C++/ASM comparison simulators remain available for baseline testing.

## Mathematical claims and models

`SmcTuring.CorrectedPaper.full_paper` combines pure-SMC simulation of each finite
source Turing machine, halting/divergence equivalence, instruction-level code
writes, a concrete unbounded distinct-field witness, an effective interpreter,
and logical tape/head observations. The interpreter journal is on a halted
configuration reached from its numbered machine's encoded input. The unbounded model uses integer addresses
and values; it can be understood as an ideal RAM machine with arbitrarily large
address encodings. The constructed image and initializer do not receive future
execution answers as inputs. Infinite changes and unbounded distinct changed
fields are separate statements. The latter has a computably initialized
five-instruction traversal in the same image, starting from the literal
identity-memory initializer with a selected primitive-recursiveness proof.
Every counted field changes,
then its owning STORE is fetched on the very next step and reads the changed
operand. A dormant storage template cannot satisfy this property.

Stephen Dolan's *mov is Turing-complete* is a separately credited foundation:
one fixed four-register program using three MOV forms and an unconditional
loop backedge simulates each finite machine. Invalid dereferences stop execution,
as in Dolan's Section 5. A stronger certificate reaches the deliberate load from
invalid address zero exactly when the source TM halts; invalid loads do not
return zero. That static program is different
from the paper's pure instruction-modifying construction. The
[Dolan formalization guide](DOLAN_FORMALIZATION.md) provides the standalone
theorem, source map and precise normalization/adaptation account.

`SmcTuring.Appendix.Listing9PhysicalBinding.full_paper` supplies conditional
bounded native refinement. It derives the full trace and each prefix from
present normalized-object/entry agreement, numeric capacity/reach bounds and
local ISA effects. Every future image, access, copy lifetime and owner certificate
is derived. [The physical contract](PHYSICAL_BINDING_CONTRACT.md) states the
coherent-fetch, flat-segment, CET-off, stable-mapping, ABI and observation
conditions. Finite x86/x64 hardware is not asserted to have an infinite tape;
the theorem does not prove an entire CPU/OS or infer a hardware RET/stop.
The head is observed before cleanup. Full seed AX restoration is at the
epilogue boundary, before the precisely described M20 x64 trailing declaration.

The [final theorem map](FINAL_THEOREM_MAP.md) identifies each result family.
The [proof ledger](PROOF_LEDGER.md) now closes the shared mathematical rows.
Dated earlier progress notes are historical, not new open proof obligations.

## Reproduction and acceptance

Lean is pinned to `leanprover/lean4:v4.35.0-rc3`, compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`; the current Mathlib pin is
`5e043698502894993991089b2dd893867c0db5c2`. The earlier acceptance source
`1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4` used
`302343bb9a029d4edab4f736703f0736896c1b64`. The aligned submission source
`a97fbd690b4051463a3b3fe86b5823823aa91bac` uses the current pin and passed
a separate cold proof audit and mechanical preflight, recorded in
[the alignment receipt](acceptance/palomar-render-compatibility.json).
The committed manifest fixes all dependency revisions. See [CI instructions](../validation/ci/README.md)
and the workflow in `.github/workflows/proof-native.yml` at repository root.
It performs fresh Linux proof checking and Windows baseline/corrected native,
MASM and normalized-object checks at the same source commit.

All local workstation verification runs serially through
`validation/limited_run.py` with its unchanged 1.5 GB allocation guard.
Full Windows Lean compilation and memory reduction are optional convenience
checks; actual Windows native/assembler evidence remains an acceptance gate.
Remote proof checkpoints are fetched to the local evidence archive at each
completed or failed check. Linux objects are kept separate from Windows objects.

[The Palomar audit](PALOMAR_AUDIT.md) separates existing mathematical evidence
from the small independent Challenge/Solution interface, Comparator, NanoDa,
official full reusable workflow, public snapshot and editorial review.
Only explicitly selected Comparator declarations can become registered claims.
No Palomar registration or endorsement is claimed.

## Provenance and audience

This is a source-based formalization and correction of known published work;
no new theorem priority is claimed. Restricted instruction computation and
verification of mutable code are relevant to computability and program
verification researchers. The metadata distinguishes background work on general
self-modifying-code verification and analysis from this pure-SMC construction.
It identifies Mathlib's prior computability formalization separately.

Gregory Morse supplied the construction, source, correction policy and project
direction. Codex generated substantial Lean proofs and validation tooling.
The cold kernel audit and agent source review are mechanical/automated evidence,
not independent human peer review. See [formalization.yaml](formalization.yaml)
for the source relationships, automation roles, completed review and limitations.
The repository code/formalization license is **CC0-1.0**; cited publisher
reference material retains its source terms.
# Publication artifacts

The compact [errata PDF](../output/pdf/morse-2018-errata.pdf),
[LaTeX source](errata/morse-2018-errata.tex) and
[minimal correction diff](errata/morse-2018-minimal.diff) are included.
The [license check](LICENSE_AUDIT.md) confirms CC0-1.0 for the formalization;
cited papers retain their publishing terms.

