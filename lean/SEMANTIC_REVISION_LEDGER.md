# Semantic consistency revision — complete

This receipt is historical for `16bd686e33c2ceff4bd3efe6c0d6e91f4e67ffc0`.
The subsequent initialization/execution strengthening and current release
state are tracked in [EXECUTION_REVISION_LEDGER.md](EXECUTION_REVISION_LEDGER.md).

All five earlier revision obligations are **COMPLETE**. Their tested public
commit is `16bd686e33c2ceff4bd3efe6c0d6e91f4e67ffc0`; the
[acceptance receipt](acceptance/semantic-revision.json) binds its source and reports.
This closes repository work. Palomar's new semantic review remains a registry decision.

| Item | Correction and positive evidence | State |
| --- | --- | --- |
| R01 | README and metadata identify the current Mathlib pin and distinguish historical acceptance. Package and protected checks pass. | COMPLETE |
| R02 | Actual deliberate invalid-zero MOV load certified iff source halts; trapping semantics match Dolan Section 5 and are disclosed throughout. | COMPLETE |
| R03 | Unbounded distinct changed fields require their owning STORE to be fetched on the next step; a pure five-instruction traversal proves the stronger property. | COMPLETE |
| R04 | Computable header decoder matches the updated image exactly; all selected definitions audited against descriptions and sources. | COMPLETE |
| R05 | Immutable full proof/native, protected mechanical and unmodified rendering checks all pass. | COMPLETE |

| Final check | Result | Actual run |
| --- | --- | --- |
| Full Lean and Windows native CI | PASS: 1,154 freshly compiled modules, zero reuse, 7,995 declarations under standard axioms; 210 fresh Windows exporter modules; 21 native suites and 30 baseline checks | [Proof/native CI](https://github.com/GregoryMorse/smcTuring/actions/runs/38228012700) |
| Protected Palomar verification | PASS: selected four theorems/four definitions accepted by Lean, NanoDa and con-ron | [Mechanical CI](https://github.com/GregoryMorse/smcTuring/actions/runs/38228020935) |
| Unmodified Challenge rendering | PASS: 997 lines / 61,802 bytes, within hard limits | [Rendering CI](https://github.com/GregoryMorse/smcTuring/actions/runs/38228023840) |

[Definition-level alignment](SEMANTIC_ALIGNMENT.md) explains the eight selected
surfaces, source citation, address normalization and explicit image assumptions.
The weaker dormant-template walker remains supporting material; the selected
distinct-field witness executes its owners. Invalid reads trap rather than
returning zero, and the positive certificate excludes arbitrary faults as
evidence of source halting.

Iteration checked only affected closures, culminating in 95 modules with
source-bound reuse. The first full candidate `a809fca525169c329fb9a99f8d78ca4d91018d80`
caught an outdated computable storage-header decoder. Its correspondence and
primitive-recursion proofs were repaired before the final cold audit above.
The failed candidate is superseded. All remote progress and final CI reports
have been archived locally; local verification used the existing memory guard.
