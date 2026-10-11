# Venue eligibility and preparation

Checked 2026-10-06 against the venues' primary policies.

Palomar can register formalizations of previously published results: its
provenance rules expressly accommodate formalizing, adapting and independently
proving known work. Publication in 2018 does not itself disqualify this project.
A credible research audience and successful mechanical/editorial checks remain
necessary; no acceptance or registration is claimed.
[Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

VibeMathed expressly excludes formalizations of results humans already proved.
This project's formalization and local errata therefore do not meet its stated
inclusion test. A distinct new answer to an open question would be a separate
proposal, with its own evidence.
[Methodology](https://vibemathed.com/methodology)

The substantive result is Gregory Morse's published pure self-modifying-code
construction. Stephen Dolan's MOV-only construction is credited as a foundation.
The corrected construction retains the paper's algorithm and records the exact
local substitutions in the compact errata. Later Lean proofs and validation
tooling were developed with Codex assistance; the original mathematical
authorship is unchanged.

The current pinned build has 3,496 audited declarations and standard axioms
only. The ideal unbounded word model proves computation, purity, arbitrarily
late modifications, a distinct-field unbounded witness, output recovery and
the effective converse. Finite x86/x64 fixtures provide reproducible realization
evidence. Their scope and the remaining literal-source/physical refinement
gates are stated in [COMPLETION_AUDIT.md](COMPLETION_AUDIT.md).

| Preparation item | Current state |
| --- | --- |
| R01: small statement/proof pair | Planned. Present the principal exact statements with only allowed Challenge imports; keep project proof modules on the Solution side. |
| R02: Comparator and independent replay | Planned. The local Lean/axiom/native audit passes; registry Comparator/NanoDa verification has not been run. |
| R03: provenance/automation/review metadata | Planned. Credit both papers, Gregory Morse as human maintainer, Codex assistance and the absence of independent human review. |
| R04: public reproducible snapshot | Planned. Select a public full commit, consistent existing license and the Lean subproject; exclude build artifacts. No commit/publication/submission was performed. |

Palomar requires a small Challenge/Solution pair, comparator configuration and
structured provenance. Its current minimum is Lean v4.35.0-rc2; the repository
uses v4.35.0-rc3 with the matching pinned Mathlib revision.
[Policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[toolchain minimum](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json)

The continuous division current-byte execution from the original placed image
is now checked, including all four results and maintained-image reuse. Remaining literal source/x64 placement and physical ISA/fetch
gates remain. The registry pair must state each theorem's proved model and
assumptions accurately.
