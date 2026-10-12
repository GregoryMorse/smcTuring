# Semantic consistency revision

This revision strengthens the correspondence between the selected mathematical
statements, executed traces and their descriptions. Earlier mechanical and
native acceptance receipts remain historical evidence for their exact sources.
The new statement is not accepted until its own proofs and checks pass.

| Item | Required correction | State |
| --- | --- | --- |
| R01 | State the current Mathlib pin and distinguish earlier acceptance sources. | FIXED; offline package check PASS |
| R02 | State the MOV stopping convention precisely and certify the actual intentional zero-address load, in both directions of source halting equivalence. | TARGETED LEAN PASS |
| R03 | Require changed-field owners to be fetched immediately on the same trace, and construct an unbounded pure witness satisfying this requirement. | TARGETED LEAN PASS |
| R04 | Check the changed dependency closure, including the effective interpreter's computable header decoder, and audit every selected definition against its description and cited model. | TARGETED LEAN PASS: 95 modules; definition-level audit complete |
| R05 | Run one final immutable proof/mechanical/render acceptance and publish the exact tested candidate. | PENDING |

The distinct-field property will require actual executed ownership; merely
assigning unused templates to data fields will not satisfy it. The MOV model
will distinguish a trapping invalid address from a successful read returning
zero. Dolan's section 5 explicitly uses an invalid-address read to stop;
the proof and prose must expose that convention and its normalized encoding.

Proof attempts will check affected modules on the authorized remote resources.
Unchanged production theorems will not be replayed between attempts. A final
complete acceptance checks the frozen candidate. Passed checks are repeated only
if a source change or a new failure requires them.

The combined targeted check compiled the new active-field module and reused 69
source-bound passing modules, then audited all four strengthened result theorems
under the standard axioms. The earlier MOV-only check established the deliberate
zero-load certificate. Local launcher peaks remained below 135 MB resident;
remote verification enforced its 7.5 GB allocation limit. Partial results are
kept separate from release acceptance. See [the definition-level alignment](SEMANTIC_ALIGNMENT.md)
for the eight selected surfaces, source citation and explicit image assumptions.

The first full candidate `a809fca525169c329fb9a99f8d78ca4d91018d80` stopped at
the old encoded storage-header decoder. The decoder now describes all new
storage instructions, with proved exact correspondence and primitive recursion.
The expanded targeted check passed five result declarations across 95 modules:
25 compiled and 70 verified reused. The replacement full candidate must pass
its own complete checks; the first candidate is not ready for submission.
