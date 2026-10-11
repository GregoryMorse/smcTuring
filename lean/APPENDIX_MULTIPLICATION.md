# Listing 11 multiplication: local repair and positive proof

The published p.129 listing implements a 32-bit modular shift-and-add
product. Signed and unsigned inputs have the same low 32-bit result. M07 makes
four local substitutions: `lbl1` to `lbl1+IMMOFFS`, exit-minus-next in the
delta expression, and names for the already present body/exit continuations.
The arithmetic body remains as printed. The exact location-annotated changes
are in [the minimal diff](errata/morse-2018-minimal.diff).

`MultiplyAlgebra.lean` contains ten checked results. The low-bit mask equals
`y % 2`, logical right shift equals `y / 2`, and the body preserves
`total + factor * multiplier` in `BitVec 32`. The shifted multiplier's natural
value is below the next smaller power of two. Therefore 32 iterations suffice
for every input, and the result is the modular product.

`MultiplyWords.lean` contains twenty-eight checked results for the actual
mutable operand words. Twelve pairwise distinct full-word fields represent
inputs, result, factor, remaining multiplier, total, delta, mask, displacement
and the three body scratch values. The 7/8/17/2 data instructions in the
initialization/guard/body/exit read current words, including current immediates.
The guard computes the corrected displacement and modular target. Block
contracts derive all field effects, low accumulator and CF, exterior-word
frames and code-write purity from static ownership. An unchanged self-store
still performs the required architectural write.

The native fixture retains the printed initialization/body, direct CALL
backedges and five-instruction stack continuations. It applies only M07's
local changes plus explicit MASM DWORD forms and local identifier aliases.
Its fourteen real fields include the code-backed stack pointer and temporary
return/address alias. `run_multiplication.py` builds and checks 11,458 x86
cases: edge/random products, both incoming CF values, all fourteen fields,
all GPRs/ESP/CF, every other code byte and reusable CALL displacement across
repeated invocations. Host setup/observation are outside the pure region.

`MultiplyLoop.lean` adds fifteen checked results connecting the actual
patched-displacement dispatch with the literal guard/body/exit data effects.
The selected loop terminates for all input pairs within 32 body passes, yields
the low-word product, restores inputs/low AX and reusable zero displacement,
and leaves CF false. The generated data trace equals actual word execution,
all reached data instructions write owned code fields, and every exterior word
is preserved. Its data trace has at most 817 operations.

These results positively validate the repair. E34-E36 now close the literal CALL/SP-continuation composition in the
selected word/register model. `MultiplyControl` checks fourteen results for
individual instruction lengths, current-field CALLs and five-step
continuations. `MultiplyBlocks` checks sixteen results for complete
initialization/guard/body/exit effects, the actual forward/backward PC
geometry, maintained stack readiness, code ownership and exact word frames.
`MultiplyExecution.correct` is one of five results constructing the complete
PC-dispatched terminating instruction trace and proving the product,
original inputs/EAX/ESP, CF=false, reusable zero displacement and endpoint.
Every word outside the twelve data slots is restored, including both
DEFSTACK metadata words. No intermediate state or branch outcome is assumed.

The six word/register modules have 88 audited declarations. E37-E40 add
70 byte-codec/effect, finite-field refinement and literal-packet results; the
ten modules total 158. E41-E45 add 82 image/packing/region/layout/data-trace
results. E46-E49 add 69 fixed-sequence/setup/CALL/complete-byte-block
results. E50-E52 add 20 complete-block simulation/loop/correctness results,
bringing the twenty-two-module total to 329. Native COFF comparison checks all 55 complete pure
packets plus four inactive owner packets, including fourteen field coordinates
and 57 exact DIR32 symbol/section/addend relocations (422 compared bytes). Lengths, PCs, the 171-byte conditional displacement and
-277-byte backedge match `ExportMultiply.lean`. Count-one SHL/SHR use MASM's six-byte D1 forms;
the data spans are 44/65/130/20 and each continuation is 30 bytes.

E50-E52 complete the live-byte fetch/owner/whole-loop bridge and E03 is checked
in the selected nonfaulting x86 byte machine. Physical ISA/configuration/fetch
remains E05. Native tests and the complete packet comparator supplement the
positive whole-byte theorem; its original image/entry/placement bounds are explicit.

Reproduce from the repository root:

```powershell
python validation/run_lean.py
python validation/run_multiplication.py
python validation/audit_errata.py --write-diff
python validation/audit_evidence.py
```

The aggregate evidence audit also requires fresh branch, kernel, split-word
and encoding reports after a Lean audit change.

## Complete byte bridge and remaining realization work

E37 adds the four exact missing x86 forms, with complete codec/length and
current-memory fetch proofs. E38 checks their whole DWORD/EAX/ESP/CF/PC effects,
byte frames, ownership footprints and fetched-step infrastructure. E39 refines
every printed data instruction and finite data sequence to the selected word
model under explicit complete four-byte separation/capacity. Mutable immediate
values are actual current field loads, and original agreement is sufficient.

E40 emits all 55 literal packets at their exact relative positions and binds
nine internal fields to offsets 136/146/157/252/275/285/295/311/378. Input/result
owners and DEFSTACK are placed independently. Its four inactive MOV packets
also emit the exact operand bytes, including DEFSTACK's address/immediate alias.
The literal form with current loads equals the checked effect translation.
Static emitted packets match MASM's actual bytes, protected constants,
destinations, owner coordinates and all address relocation targets/addends.

E41-E45 now construct the actual image. `MultiplyImage` preserves every
packet under an owned DWORD patch, including ADD and both DEFSTACK fields.
`MultiplyPacking` and `MultiplyRegions` derive complete byte separation,
finite field bounds and backing-memory gap frames. `MultiplyLayout` connects
the exact emitter to nine internal and five inactive-owner words. Its
`Admissible` condition permits arbitrary host gaps with the printed region
order and bounds the complete five regions before the x86 capacity limit.

`MultiplyData.block_linked` proves every dynamic read is the executing
instruction's own imm32. `block_placed`, `block_capacity` and `block_code_fits`
derive the static facts from that layout. `block_trace` constructs actual
current-byte fetches while preserving the whole original image invariant;
`block_image_trace` supplies that invariant from one initializer.
`block_intact` makes it reusable, and `block_refinement` checks every represented
word/EAX/CF/ESP against the selected data execution. The native comparator also
checks the formal initialized-image descriptors against all 59 packets and the
fourteen true mutable owner windows. No new erratum is required.

E46-E49 close the complete byte-block control bridge. `MultiplySetup` derives
the actual input/result/DEFSTACK/CALL values from the initializer, both stack
word windows, all printed continuation/tail positions and every capacity and
word/control separation condition. Every data block preserves both metadata
values. Fixed CALL words are read from protected bytes after arbitrary owned
mutations, while the guard CALL reads its current own displacement.

`MultiplyPaths` constructs both tail fetches and the selected five-instruction
continuation. CALL writes the actual inactive DEFSTACK address word; all seven
stores are owned. The exact alias restores the entire byte memory to its
pre-tail value, preserves EAX/ESP and clears CF. `MultiplyByteBlocks.target`
derives the current displacement equation from executed zero-test arithmetic
or protected fixed CALL bytes. `trace`, `run_pc`, `owned` and `refinement`
therefore check each COMPLETE byte block, with reusable image/stack invariants
and all fourteen finite field words. An original-image corollary derives setup
once. The guard's incoming zero displacement is an explicit maintained boundary
condition; E50-E52 now establish it for every reached guard.

E50-E52 close the complete continuous byte execution. `MultiplyByteSimulation`
relates the fourteen disjoint field words, EAX/CF, ESP and PC to the checked
word/register machine. Executed blocks preserve that correspondence and both
fixed CALL words. `MultiplyByteLoop` dispatches on the actual executed PC,
including the literal back edge, and derives every reached guard-zero boundary.
It constructs a single live-byte trace through the evolving original memory;
there is no repeated initializer or supplied future invariant.

`MultiplyByteCorrect.correct` has only these execution premises:

- The original input-parameterized literal image over arbitrary backing bytes.
- Its actual entry PC.
- The ordered complete-region placement/capacity bound `Admissible`.

The all-input word/register theorem constructs termination within 32 body passes;
the finite-field simulation derives the entire actual byte execution. The result
proves the low-word product, original input words/EAX/ESP, CF=false, displacement=0,
exact endpoint PC, reusable original-image/DEFSTACK values, every current-byte
fetch and code-owned DWORD write. Every ORIGINAL byte outside ten scratch/result
fields is equal to its initial value, including both input owners, both DEFSTACK
fields, fixed instruction bytes and arbitrary backing gaps. The proof uses equal
loaded words to recover original byte windows, rather than assuming they were
reinitialized from a fresh encoder image.

E03 is CHECKED for this selected nonfaulting/current-fetch x86 byte machine.
Full physical ISA/configuration and instruction-fetch coherence remain E05.
The printed ordered placement permits arbitrary host gaps; this theorem does
not remove its finite x86 capacity bound. No new erratum is needed: M07's four
minimal source substitutions now have complete positive byte-loop justification.
