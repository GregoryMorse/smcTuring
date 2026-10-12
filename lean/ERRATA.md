# Implementation errata and formalization clarifications

This record concerns Gregory Morse's *Pure Infinitely Self-Modifying Code is
Realizable and Turing-complete*, IJET 64(2), 123-129 (2018),
[DOI 10.24425/119359](https://doi.org/10.24425/119359).
It is a repository errata record; it has not been submitted to the journal.

The publication-ready [LaTeX errata](errata/morse-2018-errata.tex) gives one page
of minimal exact changes and one page of positive justification. The
[compact diff](errata/morse-2018-minimal.diff) and [edit manifest](errata/edits.json)
are checked against the published PDF, not inferred from the reconstruction.
`validation/audit_errata.py` verifies 60 exact excerpts and 128 positive
proof references for M01–M20. The reviewed [two-page PDF](../output/pdf/morse-2018-errata.pdf)
is published alongside the TeX and minimal diff; the final source-bound CI passes.

Errata policy: record an exact local replacement or insertion promptly, minimize
changes to the published text/algorithm, and give the corrected contract and its
positive proof. A local spelling or primitive repair does not invalidate the
checked dependency chain after its exact boundary effect is preserved. Keep
continuing full-paper proof obligations in the ledger, distinct from these
already resolved corrections. The two-sentence unboundedness clarification
specifies the idealized unbounded-address model; fixed-width x86 examples are
its bounded realizations. Variable-length address operands are one possible
idealized representation, not a claim about fixed x86 encodings.

## M01: DEFADDR's register-only load

Location: Listing 2, published p.124. The third instruction of `DEFADDR` loads
the accumulator from the address already in the accumulator. It performs no
memory write and therefore fails the strict per-instruction purity requirement.

Replace that load with a memory exchange. The following MOFFS store writes the
loaded value back to the pointed-to cell, restoring the exchange's temporary
write. The corrected implementation is [pure_smc.inc](../smcTuring/pure_smc.inc).
`DEFADDR_LEGACY` retains the original for differential regression only.

The complete macro's final memory equals its initial memory, and its final
accumulator equals the initial word at the initial pointer stored in the MOFFS
operand field. This holds even when that pointer targets the operand field
itself. The macro does **not** generally preserve the initial accumulator.

[Defaddr.lean](SmcTuring/Defaddr.lean) proves this boundary effect, equivalence of
the two macros, failure of the original's strict purity, and purity of the
correction when both addressed words are designated code fields. It also proves
purity and memory restoration for any finite number of macro repetitions.
The generic word proof has checked `BitVec 32` and `BitVec 64` instances.

The proof uses word-addressed operational semantics. Byte decoding, partial
overlap and fetch safety during temporary patches are separate contracts; the
local word proof does not assume them. Native byte component and image
initialization proofs now cover the repaired construction under explicit
bounds. Whole-kernel setup and finite loaded execution are now checked. N56-N64 apply
modeled canonical/RWX/CALL-target conditions, including rejected host endpoints. Actual mapping/configuration and
coherent hardware fetch remain physical realization obligations.
Native regression tests use distinct full-word fields and exact self-aliasing.
They deliberately exclude partially overlapping words.

## M02: Meaning of purity and unboundedness

Use two distinct requirements: every executed computational instruction writes
an actual code field, and the abstract model supports unbounded computation.
Writing an unchanged value still counts as an architectural write. Requiring a
changed byte after every instruction would be a stronger claim than these
storage-placeholder macros support.

Unbounded addresses are used in the mathematical model. Finite x86/x64 address
spaces support the corresponding computations while their explicit capacity
and representability conditions hold. A local repair of a storage primitive
does not itself prove universal or nonterminating computation.

## M03: Scope of static instruction coverage

Location: the prose between Listings 8 and 9. The paper states, "The machine
executes every single instruction at least once." That is a separate coverage
claim, and it is not a consequence of per-instruction code-write purity.

The repaired formalization proves that every reached computational instruction
writes an actual instruction operand. The native reconstruction deliberately
includes inactive MOFFS storage owners for metadata and the register/heap grid.
These owners give stored words real instruction encodings but are not invoked
as executable routines. Alignment padding and host entry/observation stubs also
fall outside the computational instruction set. The finite source may stop
before some source blocks or shared routines are reached.

Accordingly, this adapted construction does not claim execution of every
emitted instruction. The original listing's stronger coverage assertion remains
unproved here. A paper erratum should distinguish the proved reachable-write
property from static coverage instead of attributing the latter to this repair.
The generated owner inventory records `active: false` for these storage owners;
see `validation/generate_pure.py` and the finite `encoding.json` evidence.

## M04: Exact split-word meaning of OP64

Location: Listing 2 (`OP64`) and Listing 5 (`USEWORDOP64`). Applying XOR,
AND, OR, NOT or corresponding-half assignment to two 32-bit halves gives the
same 64-bit value as the corresponding whole-word Boolean operation or
assignment. This assumes that the logical halves have the required distinct
field locations and that the source-half values supplied to the operation are
correct. The algebra alone does not establish the printed exchange/copy frame.

The immediate form of `OP64` repeats the same 32-bit operand in both halves.
Its 64-bit operand is therefore `pack(data, data)`. For example, repeating `1`
assigns `0x0000000100000001`, not `0x0000000000000001`. Repeating zero or the
all-ones mask has the expected full-word clear/complement meaning.

Independent half-word ADD and SUB are not general 64-bit arithmetic:
`0x00000000ffffffff + 1` requires a carry into the high half, and `0 - 1`
requires a borrow. Without propagation the split results are respectively
zero and `0x00000000ffffffff`. Any arithmetic interpretation must propagate
the low carry/borrow or prove that it cannot occur for that specific use.
This is a restriction on the macro's general interpretation, not an assertion
that the Listing 8 Boolean-mask uses require arithmetic propagation.

[X64/HalfWords.lean](SmcTuring/X64/HalfWords.lean) checks 22 declarations:
exact reconstruction, five Boolean/assignment identities, the repeated-immediate
contract, corrected carry/borrow equations, conditional no-propagation equations,
and the boundary counterexamples. The proofs use only the permitted standard
axioms. No new native-computation assertion is accepted by the audit.
The adapted native backend uses full-width operations; this clarification
changes no emitted baseline code. Literal field placement, overlapping operand
cases, flags and supplementary byte-level purity remain S01/A02/E05 obligations.

Y04 now strengthens the value-level result with 28 positive literal
exchange/copy frame proofs in [X64/HalfFrame.lean](SmcTuring/X64/HalfFrame.lean).
The selected three-operation USEWORD32 and six-operation USEWORDOP64 forms
restore both source halves and the low accumulator, give exact MOV/XOR/AND/OR
whole-word results and CF, frame all unrelated words and write code at every
instruction. The unary two-half NOT form is also checked. Native x64 printed
patterns and x86 paired primitives each pass 17,290 cases across five operations
and both CF values, checking all operand words and non-target code bytes.
Native half-field placement/partial overlaps, arbitrary USEOP and the full
physical CPU/fetch contract remain separate; see [X64_SPLIT_FRAME.md](X64_SPLIT_FRAME.md).

## M05: Appendix branch target and storage contract

Location: Listing 10, pp.128-129. The printed parameter list is
`DoBranch(x, y, not, gt, sign)`, while its displacement expression is
`x-lbl2-OPSZ1-PTRSZ`. Here x is also the first compared field. A general branch
interface needs an independent target parameter; use
`target-(lbl2+OPSZ1+PTRSZ)` for that intended near-relative target. The current
field-word proof receives this relocation word explicitly and proves its
selection and modular target equation. It does not claim the original x field
is an arbitrary valid code-entry destination. E10 supplies a normalized finite byte transcription;
general byte/continuation-IP refinement remains open; E09 checks the printed stack/CALL
and JUMPTARGET register/word effects, including its deliberate slot/address alias.

The two operand fields and the three scratch fields must be distinct, with
full byte nonoverlap in a native implementation. The checked alias counterexample
shows that x=y can make the not-equal test sample the original accumulator;
it is not a general comparison of two original aliased values. An emitter must
separate storage or implement a deliberate constant-predicate alias case.

The `gt` flag samples SUB borrow for greater-than, or NEG nonzero for not-equal.
Complementing the mask and swapping operands give all six relations, with exact
signed sign-bit normalization and complete operand/low-accumulator restoration.
[APPENDIX_BRANCHING.md](APPENDIX_BRANCHING.md) states the parameter table and
39 checked field-word declarations, including the actual mask/relocation writes,
CF result, unrelated-word frame and conditional code-write purity.

The bracketed CALL is not itself corrected: under MASM NEAR-code-label typing,
`call [label+5]` is E8 rel32 with field +1. Only explicit DWORD PTR forces the
indirect FF /2 form with field +2. The three finite assembler comparators and
source/artifact hashes are in `validation/appendix-calls.json`. This typing
condition must be retained by a transcription; it is not portable syntax across
all assemblers. No original comparison source or published PDF has been edited.

## M06: Declared identifier spellings

Locations checked visually against the published PDF: Listing 3 p.125,
Listing 8 p.127, and Listing 12 p.129. Replace `sbb [maskptr], 0` by
`sbb [datamaskptr], 0` to use the comparison's declared mask argument.
Replace Listing 8's `IMMOFS` and Listing 12's `IMMOFSS` by `IMMOFFS`, the
already defined Table II constant `OPSZ2 + PTRSZ32` (six bytes).

These are name-resolution corrections. Substituting the declared mask argument
instantiates the same SBB-to-mask instruction proved in the comparison/branch
semantics; substituting the declared offset selects the existing full immediate
field. They do not alter the intended resolved instruction effects. The exact
source excerpts and replacements are M06a-M06c in the compact diff and are
checked by `audit_errata.py`. No claim that the remainder of literal Listing 8
or Listing 12 is already proved follows from these spelling corrections.

## D01-D03: Dolan source corrections to audit in the foundation

Source: Stephen Dolan, *mov is Turing-complete* (2013),
[PDF mirror](https://drwho.virtadpt.net/files/mov.pdf).
These observations were checked against rendered PDF pages 3-4. They are local
normalizations for formalization, not claimed author-approved published errata.

| ID | Location and issue | Normalization |
| --- | --- | --- |
| D01 | p.3 pop block uses the right-stack value as the preserved left-stack value. | Preserve the left-stack register on the right-pop path. The repository already uses this form. |
| D02 | p.4 halt lookup selects scratch when H indicates equality and invalid zero when it indicates inequality. | Swap the selector entries, or complement H. The repository implements the complemented H convention. |
| D03 | p.4 result-spill cursor advance indexes with the result register after loading one into the scratch register. | Use the scratch register containing one, as the following prose specifies. |

The foundation must also disclose the one unconditional back-edge, trap-based
halt observation, and unbounded memory. A finite straight-line MOV list does not
itself establish nontermination. The current Dolan modules now prove one fixed
64-MOV body's complete TM simulation, bounded scanning, and halting/divergence
equivalence. The intermediate body uses thirteen logical registers; a checked
scratch-ring compiler now lowers it to exactly four physical registers.

## D04: Tape initialization convention

The formalization uses a standard two-sided tape. Its initial left and right
stacks are generated by a computable blank/link template, with finitely many
input symbols. This differs from the printed initialization with an empty left
stack; it is a disclosed model adaptation, not a claim that the printed source
already handles arbitrary motion beyond its left boundary.

`Dolan/Initialization.lean` defines the signed-position enumeration and the
initial memory generator explicitly. `initial_tape_correct` proves the tape
representation. `TableLayout` and `Scan.initial_scan_correct` additionally prove
the finite transition-table encoding and complete scanner initialization.

## D05: Sentinel check before candidate dereference

The fixed loop checks whether the transition cursor equals scratch before
reading any candidate-body fields. Its nine-MOV guard saves and restores the
cursor's first word, computes the complemented equality flag, and dereferences
invalid zero on equality. It handles an initially empty list as well as a list
exhausted during scanning. This placement is a disclosed normalization of the
source control sequence. The guard restores every transition-record word and
changes only scratch memory when it succeeds.

The complete body then computes the symbol match, selects the symbol write and
head motion, and chooses either the destination-state list or the next candidate.
`Kernel.kernel_candidate_correct`, `Progress.scan_resolves`, and
`Simulation.kernel_halting_iff/kernel_divergence_iff` prove this behavior. Each
reject reduces a finite scan rank; each TM transition takes a positive number
of body passes bounded by the alphabet size. These results establish the
thirteen-register intermediate simulator. `FourCompile` and `FourSimulation`
now prove its four-register lowering and preserve halting/divergence. The pure
SMC word compiler and universality theorem are now checked in the disclosed
unbounded model. Native whole-kernel setup and its finite loaded execution are now checked.
N56-N58 apply modeled canonical/RWX bounds; physical mapping/configuration and coherent fetch remain separate
realization obligations.

## SMC backend adaptation

The reconstructed SMC implementation uses shared corrected readers rather than
duplicating one mutable address operand at multiple physical instructions.
Dynamic loads and stores enter the same MOFFS instruction. A code-backed return
field and SP reset serve every CALL; guards save their caller's return before
calling readers. An explicit offset tag check precedes the base guard, so this
backend checks arbitrary source word tags without a global offset-typing premise.

The checked 64-MOV logical kernel is lowered directly to thirteen code-word
registers using accumulator/SP hardware scratch. The independently checked
four-register Dolan theorem remains available. This is a disclosed adapted
realization, not a literal transcription of the published full listings.
Only the DEFADDR substitution is presented as the local printed-macro repair.
The original publication itself has not been edited or republished.

## Validation evidence, 2026-10-04

- All four unchanged C++/MASM configurations rebuilt and ran successfully:
  Debug/Release on Win32/x64. All 30 simulator results matched the expected
  addition example. See [baseline.json](../validation/baseline.json).
- The requested after-repair retest passed the same four configurations and 30
  outputs, with unchanged original source hashes. See
  [baseline-after-repair.json](../validation/baseline-after-repair.json).
- The native original/corrected DEFADDR harness passed 20,324 deterministic edge
  and pseudorandom cases on each of x86 and x64. Both separate targets and exact
  self-aliasing were checked. See [defaddr.json](../validation/defaddr.json).
- Setup and `ret` in the native fixture are host harness instructions, outside
  the four-instruction purity claim. The fixture explicitly enables writable
  executable code; this is an execution assumption, not a result of the proof.
- The complete reconstructed native kernel passes 109 scenarios on each of x86
  and x64, with 535 observed body passes and 107 genuine closed-loop computations.
  Whole logical register/heap effects, head/tape examples, the original addition
  output and aligned/disjoint MOFFS ownership are checked. See
  [pure.json](../validation/pure.json). This finite validation does not establish
  physical CPU refinement. The complete unbounded word-model SMC theorem is checked separately.
- Kernel proof and axiom audit evidence is recorded alongside the Lean build.
  No benchmark is treated as proof of the general computation theorem.

Cached source PDF SHA256 values used for the audit:

```text
Morse: adf6d155c941770228d416ba16ef6dc4196420739034747e1ba57361bdda1a6e
Dolan: b670dbb65c4a1945f15d237ffb4929e3a928b36e3f1c34656fc6c20d71f7e843
```
## Checked word-model proof status (2026-10-03)

The repaired pure SMC backend now has a complete guarded compiler, actual
code-backed loop and finite-input initializer in the unbounded word model.
`ConcreteSimulation.fixed_pure_smc_simulation` proves halting/divergence
equivalence and reachable instruction-level code-write purity.
`ConcreteChanges.pure_infinitely_smc_universality` proves actual changes at
arbitrarily late instruction times for every nonhalting initialized TM.
`ConcreteFreshFields.walker_unbounded_fields` proves the earlier tape walker's
owned-field property. The stronger current theorem
`ConcreteActiveFields.pure_unbounded_smc_witness` separately proves a pure
infinite run changing fields beyond every finite address bound and fetching
each changed field's owning STORE immediately afterward on that same trace.
`ConcreteTerminalTape.terminal_output_reflects` recovers the complete halted
tape and head. These are disclosed adaptations of the published construction.
They do not identify finite x86/x64 memory with an infinite tape; byte/CPU
refinement and the remaining full-paper obligations remain in the ledger.

The printed 32-bit code-backed stack alias is preserved, not repaired. With
`IMMOFFS=6` and `OPSZ2=2`, CALL temporarily writes its return IP into DEFSTACK's
MOV address operand. JUMPTARGET restores that operand from the recovered top.
E09 proves the exact alias restoration and nonwrapping CF result; its word/register
projection excludes continuation IP and byte/header/current-fetch refinement.

M05's independent-target/DWORD/imm32 normalization is now implemented by
`validation/generate_branch.py` and tested by `run_branch.py` (E10). The literal
32-bit slot/address alias is retained. E11 proves the exact packet codec and
current immediate/rel32/address-patch fetch. E15-E24 now close reference emitter execution and
continuation-IP composition. General host spacing/physical ISA remain open; the published PDF is unchanged.

E12-E14 now connect the normalized branch prefix's selected byte-instruction
effects to its finite disjoint field-word proof, including all-relation
selection, operand/EAX/ESP/CF and exterior-byte restoration. The
reference emitter's own-immediate/header identities and continuous live fetch,
byte-tail return/address alias and both continuation PCs are now composed by
E15-E24. General host spacing and physical ISA/fetch remain open. No physical ISA/fetch claim or published PDF change is inferred.

E15-E19 now construct the reference emitter's complete live-byte predicate/patch
prefix from one initial image, entry and extent bound: actual x/y words, seven
real owners, own imm32 identities, protected constants/headers, field layout,
every fetched form/next PC and all-relation register/word/CF/exterior-byte results.
The native comparator checks 158 complete prefix packets and their exact own
operand coordinates against twelve Lean emitter exports. E20-E24 close the complete reference byte-tail/return-alias/continuation
execution and PCs. General host-spacing and physical ISA/fetch remain open. See [APPENDIX_BYTE_IMAGE.md](APPENDIX_BYTE_IMAGE.md).

E20-E24 add 56 checked declarations closing the complete reference x86 branch.
One initialized byte image supplies every actual fetch through the predicate,
stack exchange/CALL and selected five-step continuation. Its actual target and
both end PCs are derived; EAX/ESP restored, CF=false, every reached DWORD write
code-owned, all protected packets intact and every original byte outside the
three final scratch fields restored. CALL's temporary DEFSTACK address word is
included. Only initial image, entry and finite extent are execution premises.
The endpoints are finite observation boundaries, not source halt. General native
host spacing and physical ISA/fetch/other architectural state remain separate.
See [APPENDIX_BYTE_IMAGE.md](APPENDIX_BYTE_IMAGE.md).

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

## M07: Listing 11 multiplication branch plumbing

Published p.129 needs four local substitutions, with no change to the
shift-and-add body:

```diff
- mov [lbl1], ($-lbl9)-($-lbl3-OPSZ1-PTRSZ)
+ mov [lbl1+IMMOFFS], lbl9-lbl3-OPSZ1-PTRSZ
- JUMPTARGET() // first occurrence
+ JUMPTARGET(lblbody)
- JUMPTARGET() // second occurrence
+ JUMPTARGET(lbl9)
```

The delta goes into the AND immediate rather than its opcode, and equals
exit-minus-next. The labels name the existing body and exit continuations.
`MultiplyWords.guard_target` proves the actual patched word reaches exit
exactly for a zero multiplier. Literal initialization, body and exit effects
restore the low accumulator and preserve inputs/unrelated fields;
`MultiplyAlgebra.step_invariant` and `full_word_product` prove the invariant
and termination/product after at most 32 body passes. Complete-word separation
and the existing code-backed stack contract are explicit.

`run_multiplication.py` passes 11,458 corrected literal x86 runs, checking the
low-word product, all fourteen fields, every GPR/ESP/CF, every exterior code
byte and repeated calls without resetting the CALL displacement. Host setup
and observations surround the pure region. `MultiplyLoop.full_product` now connects the actual patched-displacement
dispatch to the printed data blocks for all inputs. Whole-data-trace purity,
input/AX/CF/displacement restoration and exterior-word frame are also checked.
E34-E36 now prove complete selected word/register CALL/SP execution and restoration. Live-byte fetch/layout composition continues in E03/E05. See [APPENDIX_MULTIPLICATION.md](APPENDIX_MULTIPLICATION.md).

E37-E40 add 70 checked multiplication byte-form/refinement/packet declarations,
for 158 multiplication proofs in total. Native comparison now checks every one
of the 55 pure and four inactive owner packets (422 bytes), fourteen actual
field coordinates and 57 DIR32 symbol/section/addend relocations. This is the
initial emitter comparison; deriving the complete continuous current-byte loop
from one original image remains E03/E05. M07 and the compact errata are unchanged.

E41-E45 add 82 checked multiplication image/layout/data-trace declarations,
for 240 multiplication proofs in total. All fourteen mutable owners, complete
byte separation/capacity and actual own-immediate data fetches are derived from
the printed layout. Every data block retains the original image invariant and
refines the selected word effects. Native initial-image descriptors match all
59 packets and their true owner windows. Full byte CALL/continuation/loop
composition remains E03/E05. The compact errata is unchanged.

E46-E49 add 69 checked multiplication fixed-sequence/setup/CALL/complete-byte-block
declarations, for 309 multiplication proofs in total. The original image now
supplies input/result/DEFSTACK/CALL values and all word/control separation facts.
Actual byte XCHG/CALL and each selected continuation compose with the data
blocks, with arithmetic-derived transfer/endpoint PCs, owned writes, reusable
image/stack invariants and fourteen-field/EAX/CF refinement. Control restores
all pre-tail byte memory and preserves EAX/ESP. Whole byte-loop/product and
exact original exterior-byte-frame composition remain E03/E05, alongside
physical whole-state realization. The compact errata is unchanged.

E50-E52 add 20 checked multiplication block-simulation/continuous-loop/original-image
correctness declarations, for 329 multiplication proofs in total. E03 is now
checked in the selected finite x86 byte model: original image/entry and ordered
complete-region placement/capacity suffice for the whole actual-PC/current-byte
loop, all-input product/termination, only code-owned writes, input/EAX/ESP/CF/
displacement/endpoint and reusable image/stack values. Every original byte outside
ten scratch/result fields is restored, including input and DEFSTACK owners and
arbitrary backing gaps. Physical ISA/configuration/fetch remains E05; other
full-paper literal/algorithm/registry obligations remain intact. The compact
errata is unchanged; M07's four edits have complete positive byte-loop proof.

M07 now also has the positive whole-byte theorem
[`MultiplyByteCorrect.correct`](SmcTuring/Appendix/MultiplyByteCorrect.lean):
one literal original image and entry, with the printed ordered placement/
capacity bounds, yield terminating live-byte execution, the all-input low-word
product, original input/EAX/ESP restoration, CF/displacement/endpoint, only
owned code writes and the exact original exterior-byte frame. The four source
substitutions and two-page TeX/PDF/minimal diff are unchanged. Physical ISA/
configuration/current-fetch realization remains the separate E05 contract.


## M08: Listing 6 constant-multiplication bit gaps

Printed p.125 needs three local substitutions: Leading to Trailing in NLZ's
description, and +1 in the two SHL counts after the first retained bit. Keep
the identifier, initial shift, USEWORD32 triples and final ADD structure.
Four exact excerpt entries include those changes and a short local convention
for unsigned 32-bit constant patterns, signed low-word multiplication,
mathematical compile-time shifts (including 32), a single zero store, omission
of an initial zero-count SHL and two distinct complete code-operand fields.

`ConstantAlgebra.correct` and `signed_low_product` prove the all-input product.
`ConstantWords.contract` proves it for the complete compiled word trace with
arbitrary original scratch, restored EAX, every legal code-word write, exact
exterior-word frame and a 128-instruction bound. `program_legal` derives all
emitted SHL counts in 1..31. These are positive correction theorems, not input
preconditions encoding the desired result.

The finite native reconstruction passes 54,366 runs across 663 constants,
including every one-bit/two-bit pattern, all GPRs/ESP/CF, scratch, exterior bytes
and repeated use. The independent Lean compiler comparator matches 11,350
complete pure packets and 79,534 original-image bytes. The printed coefficient
baseline and unchanged original comparison-source baseline are distinct.
See [APPENDIX_CONSTANT_MULTIPLICATION.md](APPENDIX_CONSTANT_MULTIPLICATION.md).
The full constant-emitter byte contract is now checked; remaining Listing 6
auxiliary operations and physical ISA/fetch stay E01/E05.
The standalone M01-M08 TeX/PDF is still two pages; its audit checks 19 exact
published excerpts and 48 positive proof references, now also including M07's
complete original-image byte theorem.


E56-E62 add 99 positive byte-codec/effect/refinement/image/packing/current-fetch
and all-input composition proofs for M08. `ConstantSimulation.original_image_correct`
constructs a real live-byte trace and low-word product, EAX/ESP restoration,
only owned DWORD writes, reusable image and exact original exterior bytes,
under original initialization and static placement/own-immediate/ownership/
capacity facts. CF and endpoint are also refined. The actual checked Lean
codec now matches every native packet and owner offset; the 54,366 cases and
11,350 complete pure packets remain green. Deriving those static facts for the
entire variable emitter and remaining auxiliary operations stays E01/E05.
No further article correction is needed; the two-page minimal errata is unchanged.


E63-E66 now discharge those variable-emitter static identities. The 184-proof
constant chain includes `ConstantCorrect.correct`: one original image, entry
and full extent bound imply actual live-byte trace, input product, restored
EAX/ESP, owned writes, reusable Intact image, exact CF/endpoint and original
exterior bytes. `reusable_correct` permits arbitrary current data/scratch and
proves the complete repeated-use contract. Actual complete Lean geometry and
owners match every native initial image, with all existing native cases green.
This strengthens M08's positive proof without changing its three substitutions,
local conventions, nineteen-excerpt diff or two-page TeX/PDF.


## M09: Listing 6 DEFZERO immediate width

The exact p.125 line becomes
`labelname: xor SZW32 ptr [labelname + IMMOFFS], CNSTFRC32`.
This adds explicit DWORD typing and substitutes the existing force-32-bit
constant for zero; the single self-targeted XOR and offset are retained.
Its complete current imm32 v is also its destination word, so v XOR v=0.

`ZeroImage.correct`, `original_image_correct`, `effect`, `intact_after` and
`reentry_trace` prove the full positive current-byte zeroing, EAX/ESP/CF/PC,
owned store, exact exterior-byte frame and live reuse contract. MASM and the
actual Lean codec agree on the complete operand packet; the corrected native
macro passes 9,312 executions on each architecture. The typed printed
baseline records the short imm8 encoding separately. See
[APPENDIX_ZERO.md](APPENDIX_ZERO.md) for the precise universal/native scope.

M09 was cleared immediately after discovery and positive proof: the exact
twenty-excerpt diff and two-page publishable TeX/PDF now include it, with
53 individually audited correction references. Conversions, division and
remaining literal/physical work continue in the full ledger.

## M10: Listing 5 declared cursor operands

The six local memory operands now address the fields just declared by DEFDATA,
using source/dest + DATAOFFS (IMMOFFS in 32-bit mode, zero at the 64-bit MOFFS
field label). The original exchange/MOVS/exchange/subtract algorithm is retained.
Listing 6's example includes its source/destination cursor labels. Forward DF,
complete region/field separation and representable pointers/SUB size are stated.

`StringPlan.correct` and `literal_widths`, `StringCursor.pair_correct`, and
`StringFields.prepared_source`, `effect` and `frame` prove the positive copy,
index/cursor restoration and exact unified-byte result. Corrected literal native
whole macros pass 6,144 executions per architecture and complete macro codec/
geometry comparison. The typed printed baseline is retained. No larger algorithm
replacement is needed. See [APPENDIX_TRANSFER.md](APPENDIX_TRANSFER.md).

The minimal 28-excerpt diff and compact two-page publishable TeX/PDF include M10,
with 59 positive correction references. Whole macro live-fetch and copied-template
relocation/decoding proofs continue in P04; all other goal gates remain intact.


## M12: Listing 2 reusable terminal marker

Replace `mov [$], 0` by `mov SZW32 ptr [$+IMMOFFS], 0`. This specifies
DWORD width and directs the existing zero store to its own immediate field at
offset six. Add: "Observe termination immediately after this marker; host
stopping and output handling lie outside the pure computation."

The same ten-byte instruction now preserves its live encoding. The positive
`Native.TerminalMarker.correct`, `pure`, `reusable` and `output_preserved`
proofs derive its actual current-byte fetch/store, observation PC, AX/SP/CF,
whole-memory/output preservation and nonempty code-owned write in both modes.
The native fixtures each pass 4,128 corrected and 4,128 typed-original cases;
all loaded/object bytes, complete register/flags/code frame and reentry are
checked. See [the terminal contract](APPENDIX_TERMINAL.md).

The correction was cleared into the exact diff and compact two-page TeX/PDF
after positive proof and native/assembler checks. M01-M12 now comprise 35 exact
source excerpts and 74 local positive proof references. The earlier counts in
this file describe historical checkpoints. Full literal source/finalization
composition, x64 field conventions and physical ISA/fetch work continue.


## Listing 9: unchanged sequence positively proved

E139-E143 now prove the printed four-instruction full-width accumulator-save
sequence and actual body/epilogue/terminal composition. The entry MOV saves AX;
the first exit XCHG/MOV restores the pointer field and all memory; the final
XCHG restores the entry accumulator and resets its save slot to its own address.
Code-owned writes, current-byte fetches, SP/CF, output frames, original pointer
bytes and live reuse are checked under the stated reserved-field/body contract.
The native fixtures each pass 38,400 cases with complete loaded/COFF comparison.
See [the positive accumulator contract](APPENDIX_ACCUMULATOR.md).

No paper edit was established by this check. The M01-M12 minimal diff and
compact two-page publishable TeX/PDF retain 35 exact excerpts and 74 local
positive correction references. The new complete audit has 3,572 declarations
and 378 ledger IDs; thirteen native suites and the aggregate evidence audit
pass. Literal Listing 8 must still establish the body contract, and optimized/
x64 field placement and physical realization remain explicit in the ledger.

## M13 - Listing 8 input-symbol source operand, p.127

The exact minimum change is curinputval to curinputval + IMMOFFS in the
USEWORD32 call writing inputupdate + REGIMMOFFS. COMPARE32 labels its first
SUB instruction; the symbol resides in its forced DWORD immediate at offset
six. USEWORD32 reads the supplied address directly. The target XOR's immediate
is at offset three. The original exchange/store/exchange sequence is retained.

E144-E145 record fifteen positive proofs and both native fixtures: the live
source symbol determines the full patched target packet, the source is restored,
AX/SP/CF and complete source/header/exterior frames hold, and all three writes
are to code fields. Each architecture passes 6,400 corrected and 6,400 typed
original cases, including unchanged-image reentry, with all twelve full loaded
and COFF packets matching actual Lean. The x64 DWORD contract includes low-AX
zero extension; universal long-mode DWORD byte execution remains separate.

The correction has been immediately incorporated into the exact excerpt diff
and the visually checked two-page publishable TeX/PDF. M01-M13 contain 36 exact
excerpts and 79 local positive proof references. The new checkpoint has 3,587
audited declarations and 380 unique ledger IDs. See
[APPENDIX_INPUT_OPERAND.md](APPENDIX_INPUT_OPERAND.md).

## M14 - Listing 8 DWORD scalar declaration, p.127

Replace the one call DEFDATA(0, curtinputval) by
DEFDATA32(curtinputval, 0). Listing 2 defines the latter with label first and
data second. Both consumers name curtinputval + IMMOFFS, the four-byte immediate
at offset six of that existing ten-byte DWORD packet. This binds the intended
name, width and field position without changing the comparison algorithm.

Seventeen positive both-mode current-byte proofs derive initial zero, the whole
packet after any live operand patch, its actual fetched self-store, PC advance,
full AX/SP/CF, unchanged whole memory, output frames, purity and reusable code.
The live candidate symbol is preserved when the owner executes. Each architecture
passes 6,400 native cases and all forty live packets plus the zero initializer
match Lean; the complete COFF packet and DIR32/REL32_4 target/addend are checked.

The exact excerpt diff and publishable TeX/PDF were immediately updated after
these proofs and native/assembler checks. M01-M14 now contain 37 source excerpts
and 83 local positive references in two pages. See
[the positive scalar owner contract](APPENDIX_DWORD_OWNER.md).

## M13 both-mode proof strengthening - 2026-10-06

E148-E153 close the universal long-mode DWORD helper gap with 77 positive
declarations. InputDword.copy_correct derives the live source symbol and whole
target encoding from actual current-byte fetches in both modes. All three stores
write four bytes; EAX is restored and x64 RAX is zero-extended. Source/header/
exterior frames and SP/CF hold. Natural long-mode addresses retain all bits.

The exact paper diff is unchanged. The existing native fixtures now compare
all helper packets against the actual model, verify all nine proved static
checks and cover real x64 addresses above 4GiB. The compact two-page TeX/PDF
selects the stronger proof reference; 37 exact excerpts and 83 positive local
references are retained. See [APPENDIX_DWORD_COPY.md](APPENDIX_DWORD_COPY.md).


The DWORD comparison/input-selection checkpoint adds 53 positive supporting
proofs without another correction. The packed reset/SUB/NEG/SBB/NOT forms
produce the exact equality mask for every DWORD in both modes, with actual
current-byte fetch, scalar/mask/full-AX/SP/CF/PC/purity and exterior frames.
The XOR/AND identity and final base-addressed tape XOR step are also checked.
The printed interleaved copy/owner and cursor exchanges remain to compose;
[the checkpoint document](APPENDIX_DWORD_COMPARISON.md) states that scope.
M01-M14, 37 exact source excerpts, 83 local errata references and the compact
two-page TeX/PDF are unchanged.


### M04 register-width precision (2026-10-06)

The compact M04 insertion now also states the exact DWORD helper frame:
EAX is restored; in x64 mode RAX is its zero extension. A zero-extended entry
RAX therefore gives full RAX restoration. This is the existing positive
Native.DwordEffects.effect / Appendix.InputDword.copy_correct result, including
arbitrary upper entry bits. The assembly stays the same. The exact diff still
has 37 published anchors and 83 registered positive proof references.
The TeX and diff are updated. The coordinator rebuilt the two-page PDF and
visually checked both pages with Poppler; the first-page text uses 9 pt/9.8 pt
leading to preserve the compact layout. The remote Linux proof audit now passes
with its current source hashes; bounded Windows/native refresh remains pending.


## M15: Listing 8 comparison-mask copy fields (2026-10-06)

The two USEWORDOP64 calls targeting `ttapevalmask + IMMOFFS` and
`inpdirmask + IMMOFFS` pass `inputvalmask, IMMOFFS` as their final arguments.
Replace those arguments, in each call, by `inputvalmask + IMMOFFS, 0`.
The low source must be the AND instruction's DWORD mask immediate at offset
six. The x64 high source must be that same immediate, because a Boolean
comparison mask is replicated to both logical destination halves.

The original page 127 was visually inspected and both exact excerpts match
the source PDF with SHA-256
adf6d155c941770228d416ba16ef6dc4196420739034747e1ba57361bdda1a6e.
`Appendix/Listing8MaskCopy.lean` proves a closed original-source counterexample
(the zero-displacement AND header reads 0x2581), the correct live immediate
field, the universal both-mode three-step mask copy and source restoration,
and the actual six-step x64 replicated-mask trace/effect under explicit static
field/range conditions. These are positive corrected contracts; no future
execution or mask result is assumed. The two initial helper images are
byte conditions on one memory. Full literal placement and native packet
binding remain larger composition obligations.

The exact edits, deterministic diff and compact TeX were updated immediately.
The M01-M15 PDF was rebuilt with task-local Tectonic 0.17.0, remains two pages,
has no overfull box/undefined-control warning, and both pages were visually
checked. The correction inventory is now 39 exact excerpts and 91 positive
proof references. Complete Linux axiom evidence is refreshed at turn end;
fresh Windows/native aggregation is still required.


## Current M15 source-bound evidence (2026-10-06)

The complete exact-rc3 Linux audit passed with 369 production modules,
3,961 declarations and 398 Lean-source/helper hashes. All 16
`Listing8MaskCopy` theorems are included; only propext, Classical.choice and
Quot.sound occur. The current report SHA-256 is
9437028e732e1bfd7f79c6a97fbc701def732044b28ba00321344bb1989f6012.
The mask-copy source SHA-256 is
1cf1a66e6f6c900fcc7b59a4c237ba4a1b55d759b351dd9ed675fda2cec726df.
`validation/remote-evidence/errata-source-proof.json` passes all 39 exact
source excerpts, 91 positive correction references and current two-page PDF
text/log checks. Both PDF pages were visually checked. Earlier audit/PDF
hashes in this document are historical; fresh Windows/native aggregation
and the complete literal interpreter are still required.


## Integrated M16-M19 corrections and current evidence (2026-10-06)

The current inventory is M01-M19: 55 exact excerpts and 121 audited references. Earlier counts and hashes above are historical. The exact compact replacements are in `errata/morse-2018-minimal.diff` and `errata/edits.json`; their detailed positive justification is in `errata/README.md` and the two-page TeX/PDF.

M16/M17 add the generalized input node's two neighbor owners and use entry/end labels for complete node/transition copy extents. `Listing8Prototypes` and `Listing8PrototypeCopy` prove the complete values and copies; the global initializer derives both actual copies and retargeted owners from one initial image.

M18 applies the already established DATAOFFS to Listing 8 cursor reads/writes. M19 selects the pending XOR immediate fields and their ten-byte packet spacing, while the source and destination pointer halves retain four-byte spacing. `Listing8CursorFields.source_cursor`, `Listing8PointerTargets.immediate_patch`, the pointer-half effect/selection facts and `Listing8PointerValues` give the positive corrected contracts. Full later control/loop composition remains open.

Checkpoint 8f92ac6 is now integrated. Its complete Linux audit passes 4,327 declarations; the targeted Windows audit passes 541 declarations for the 39 changed modules. The locally rebuilt two-page PDF has been visually inspected, and all 55 source anchors and 121 proof references pass the focused source/PDF check. Full Windows/native aggregation remains pending after the unchanged DivisionSetup module reached the enforced memory guard. See the local integration section in COMPLETION_AUDIT.md and validation/remote/157.181.172.78/20261006/latest-integration.json for exact scope and resource records.

## Integrated M20: Listing 9 storage operands (2026-10-07)

The current compact inventory is M01-M20: 60 exact excerpts and 128 positive
proof references. M20 applies the already defined DATAOFFS to four memory operands
and the pointer declaration's initial save-label value. These five substitutions
select the stored word instead of the x86 instruction header while retaining the
x64 operand location, instruction order and save declaration. The exact changes
are in `errata/morse-2018-minimal.diff` and `errata/edits.json`.

`Listing9Fields`, `Listing9PackedLayout` and `Listing9ExecutionImage.execute`
positively prove the repaired fields, initial pointer, layout bounds and actual
entry/body/epilogue. `Listing9FullExecution.execute` also joins both trailing
declarations. Full seed AX is restored at the third-epilogue boundary; x86 retains
it through trailing fallthrough, while x64 then has the save-field address in RAX.
Physical stop, return and ABI claims remain separate. The two-page TeX/PDF states
the restoration boundary explicitly; no additional paper edit is established by
the exact fallthrough theorem.

Checkpoint 25188e2 is integrated with a complete source-matched Linux audit of
741 modules and 6,107 declarations. The compact PDF was rebuilt locally and both
pages inspected, together with published pp.124/127. All 60 source excerpts and
128 proof references pass. Prior counts and audit hashes above are historical.
Complete body purity, TM compilation and fresh Windows/native aggregation remain
open; the local resource cap is unchanged.
