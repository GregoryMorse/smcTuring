> Current closure (2026-10-11): all seven rounds are accepted. Complete public
> proof/native CI and Palomar full mechanical preflight pass. See
> [closure status](CLOSURE_STATUS.md) and [final acceptance](FINAL_ACCEPTANCE.json).
> Dated progress comments below are historical and do not reopen closed obligations.

# Listing 10 branching contract

Date: 2026-10-05. The printed predicate and displacement-patching prefix is
checked in a 32-bit field-word model. E12-E14 now refine the selected byte
effects to the finite field-word prefix,
including all-relation displacement/register/word/CF and exterior-byte results.
E15-E19 construct the reference prefix's current-fetch execution from one
initial image. E20-E24 close the reference tail/continuation trace and both end PCs. General
host spacing and physical CPU state/fetch remain open. E10 checks a finite real byte layout/native fixture; E11 checks
packet encoding and current operand-patch fetch. E09 checks the stack/CALL and
JUMPTARGET register/word effects and their relation composition. The whole
appendix and physical x86 realization remain open.

## Literal source and conventions

The source is Gregory Morse's 2018 paper, Listing 10, published pages 128-129,
DOI 10.24425/119359. Both pages were rendered and visually checked against the
cached PDF, whose SHA256 is
`adf6d155c941770228d416ba16ef6dc4196420739034747e1ba57361bdda1a6e`.
The prefix preserves the printed order: zero the CALL displacement and SBB
mask, optionally flip the sign bits, exchange the first operand, subtract it
from the second, optionally negate before and after the mask SBB, restore both
operands and the accumulator, optionally complement the mask, and patch the
AND immediate and CALL displacement. Mutable mask/delta operands are read
from the actual resulting field state; no selected result is supplied as input.

`Machine32` observes the low 32-bit accumulator, CF and all logical field words.
It does not promise preservation of the upper half of RAX, every flag, or the
entire CPU. Its NEG CF law and NOT flag preservation were checked against the
SHA256-pinned Intel SDM revision 093, volume 2B PDF pages 166 and 169. Other
selected SUB/SBB/ADD/AND/XOR rules use the already pinned selected ISA references.
This reference audit is not a formal whole-ISA or hardware-fetch theorem.

## All six relations

The printed `gt` flag selects SUB borrow for greater-than, or NEG nonzero for
not-equal. The printed `not` flag is named `notFlag` in Lean: true keeps the raw
mask and false complements it. The missing relations use an operand swap.

| Intended relation | Operand order | gt | notFlag |
| --- | --- | --- | --- |
| x < y | y, x | true | true |
| x <= y | x, y | true | false |
| x = y | x, y | false | false |
| x != y | x, y | false | true |
| x > y | x, y | true | true |
| x >= y | y, x | true | false |

For signed comparison, XOR with `0x80000000` has the checked identity
`Int(flipped.toNat) = original.toInt + 2^31`. Thus its unsigned order is exactly
the original signed order, for every bit pattern including the signed minimum
and maximum. Equality is bit-pattern equality and is unaffected by the flip.

## Executed prefix and complete state result

Five logical fields are distinct: x, y, mask, CALL displacement and AND delta.
Byte-level disjointness/alignment is a later layout requirement; distinct logical
coordinates alone do not prove it. `Branching.comparison` follows the literal
comparison and restoration instructions. `Branching.program` also includes
the initial displacement zero and the final actual mask/delta/displacement writes.
`relationProgram` supplies the table above, including real operand swaps.

For any initial accumulator, CF and field memory, every signed/unsigned relation
has these checked effects:

- The actual patched displacement is delta exactly when the requested relation
  holds, and zero otherwise.
- Both operands and the low accumulator are restored. Every field other than
  the three scratch fields is restored. The final scratch words are explicit:
  delta holds the supplied relocation word; mask and displacement hold the
  selected relocation word. Final CF is false.
- With delta = target - next, fixed-width `next + patchedDisplacement` is target
  on the selected branch and next otherwise. This is the x86 modular target
  equation; it does not assert canonical/mapped instruction fetch or a valid
  stack/CALL execution.
- Every prefix instruction writes its stated destination. If all five fields
  are actual owned instruction operands, the whole prefix has code-write purity.
  Constructing the literal byte owners and protecting opcode headers is part
  of E05 and the byte refinement, rather than a conclusion of this field model.
- The prefix length is exactly 10 + 4*signed + 2*(!gt) + (!notFlag), from 10 to
  17 events. It ends before the printed stack exchange and CALL.

`alias_counterexample` proves that field separation cannot be omitted. With
x and y at the same field containing zero and accumulator one, the not-equal
prefix selects a nonzero delta even though the original operands are equal.
A general emitter must use distinct scratch storage or recognize an aliased
comparison and emit the known constant predicate. No such alias normalization
is silently included in the literal prefix proof.

## CALL typing and the target parameter

The paper's `OPSZ1=1` and `PTRSZ=4` suit the five-byte E8 near-relative CALL.
Under MASM NEAR-code-label typing, `call [label+1+4]` emits exactly that form;
the brackets do not force an indirect call. An explicit `DWORD PTR` emits the
six-byte FF /2 indirect form with its address field at +2. The reproducible
three-way comparator is [appendix-calls.json](../validation/appendix-calls.json),
generated by [audit_appendix_calls.py](../validation/audit_appendix_calls.py).
This is finite assembler evidence, not a proof of every assembler or declaration.

The printed parameter list has no independent branch target: its relocation
expression uses x, which is also the first compared field. For a general branch
interface, M05 proposes an explicit target parameter and the expression
`target - (lbl2 + OPSZ1 + PTRSZ)`. The current theorem takes the relocation word
as input and proves its actual selection, then the modular target equation.
It does not assert that the literal first-operand address is an arbitrary valid
branch destination.

## Remaining E02/E05 work

- E10 supplies the normalized emitter with DWORD types, imm32 owners and an
  independent target, and verifies finite real offsets/owners/header separation.
  E12-E14 now compose selected byte effects with the proved field-word prefix.
  E15-E19 now derive reference emitter layout/ownership and each dynamic source
  field's identity with its own immediate. General host-spacing remains separate.
- E15-E19 now derive the complete reference prefix's live fetch, protected
  headers/constants and nonwrapping PCs from one initial image/extent/entry.
  E20-E24 retain this same evolving image through the two tail and five selected
  continuation steps. Actual endpoint PCs, headers, owned return/address write
  and exact register/full-byte restoration are now checked for the reference.
- Generalize to independently spaced host continuation regions and retain the
  explicit physical ISA/configuration/coherent-fetch realization conditions.
- Retain E10's passing whole native regression and direct Lean-shape/MASM
  provenance while refining the general construction. An unexpected fault is
  still a fixture failure rather than intended source termination.
- Retain the original register/flag and the other appendix algorithm obligations.

The full root import and standard-axiom audit include all 39 declarations in
`Appendix/Machine32`, `Appendix/BranchAlgebra` and `Appendix/Branching`.

## Checked printed x86 stack/CALL and continuation

`Appendix/BranchTail` adds 23 root-imported, standard-axiom-audited declarations.
Listing 4 on published page 125 was rendered and visually checked for this step.
This is the printed single XCHG followed by E8 CALL, rather than the adapted
native backend's two-instruction stack reset. The CALL displacement is read
from the actual field state after XCHG and before CALL's push.

At the tail boundary, let pointer be the `stptr+IMMOFFS` field, oldTop its
original word, oldSP the incoming ESP, returnSlot = oldTop - 4, and next the
CALL's next IP. XCHG stores oldSP at pointer and sets ESP to oldTop; CALL
writes next at returnSlot, sets ESP to returnSlot, and jumps to next plus the
actual current displacement. Accumulator and CF survive these two instructions.
The x86 selected absolute XCHG/E8 sizes used here are 6 and 5 bytes; this does
not establish the preceding prefix's byte length or its entry layout.

The five actual JUMPTARGET register/word operations are:

1. XCHG ESP with pointer, recovering oldSP and storing returnSlot at pointer.
2. ADD pointer,4, restoring oldTop and defining the final CF.
3. XCHG EAX with pointer, temporarily loading oldTop and storing the old EAX.
4. MOV the actual EAX into the defining MOV's address field.
5. XCHG EAX with pointer, restoring EAX and oldTop.

The deliberate source alias is essential. `IMMOFFS=6` and `OPSZ2=2`, so the
printed DEFSTACK top is its defining MOV's immediate address, and CALL pushes
four bytes earlier into that same MOV's address operand. The checked
`continued_alias` and `continued_alias_no_carry` contracts explicitly use this
slot/address identity and require the original address and immediate to hold
the same top. The continuation restores **all boundary field words and ESP**;
the temporary return IP is overwritten by the restored top. It is not a saved
return word that remains after JUMPTARGET. A separate `continued_return`
theorem covers an independently allocated disjoint-slot variant.

With oldTop.toNat >= 4, the continuation's ADD has CF=false. This is a proved
nonwrapping arithmetic condition, not a claim about a valid physical stack.
`branch_pc` composes every actual signed/unsigned prefix with the literal tail
and gives target on the selected relation and next otherwise. `branch_restored`
composes the alias continuation: prefix scratch results remain, original ESP
and low accumulator are recovered, all prefix-boundary words are restored and
CF=false. `branch_pure` covers the actual prefix, two tail writes and five
restoration writes when their destinations are owned code fields.

This milestone is at the field-word/register level. The continuation projection
intentionally excludes IP; no byte count, valid fetch at either target/next,
general header/execution composition during the temporary address overwrite
or full CPU state is asserted by E09. E10 now supplies the finite whole native
regression; E11 proves current address-patch packet fetch with header/imm32 preservation. Both endpoints must have the right
JUMPTARGET byte sequence in the later emitter. Distinct logical fields do not
by themselves prove byte nonoverlap or legitimate instruction operands. E02/E05
remain IN_PROGRESS for those explicit requirements.

[APPENDIX_BYTE_CODE.md](APPENDIX_BYTE_CODE.md) records E10's 74,400 native
cases and exact finite layout/owner/frame checks, plus E11's 24 packet-level
codec/current-patch proofs. Neither milestone is a full general branch byte trace
or physical hardware refinement; E02/E05 stay IN_PROGRESS.

E12-E14 add 68 checked selected-byte/finite-field declarations. See
[APPENDIX_BYTE_CODE.md](APPENDIX_BYTE_CODE.md) for the instruction rules, field
capacity/separation contract, exact branch byte-state results and remaining
literal emitter/actual-fetch/tail/continuation obligations. A supplied trace is
still an explicit premise of the E14 trace corollary; E19 now constructs the reference prefix trace.

E15-E19 now construct the reference emitter's complete live-byte predicate/patch
prefix from one initial image, entry and extent bound: actual x/y words, seven
real owners, own imm32 identities, protected constants/headers, field layout,
every fetched form/next PC and all-relation register/word/CF/exterior-byte results.
The native comparator checks 158 complete prefix packets and their exact own
operand coordinates against twelve Lean emitter exports. E20-E24 close the complete reference byte-tail/return-alias/continuation
execution and PCs. General host-spacing and physical ISA/fetch remain open. See [APPENDIX_BYTE_IMAGE.md](APPENDIX_BYTE_IMAGE.md).

E25-E30 add 72 checked declarations for independently spaced, ordered forward
x86 branch blocks. One original byte image supplies all pure fetches; the actual
Taken-Fall displacement, both continuation end PCs, EAX/ESP/CF restoration,
every owned DWORD write and exact host-gap backing bytes are derived. The native
comparator now checks all 338 complete pure packets at the actual twelve COFF
layouts, including target constants, destinations/owner coordinates and end PCs.
Only absolute payloads are normalized, with separate symbol/addend/relocation
checks. The actual host gaps are 50/12/76 bytes. Other region orderings/backward
geometry and physical ISA/configuration/coherent fetch remain separate.
See [APPENDIX_BYTE_SPACING.md](APPENDIX_BYTE_SPACING.md).
