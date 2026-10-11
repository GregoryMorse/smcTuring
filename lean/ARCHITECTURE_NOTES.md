# Native realization record

## Current acceptance — 2026-10-11

Mathematical proofs and conditional native/head/COFF bindings are complete;
rounds 1–6 are accepted at immutable passing checkpoints. The final cold replay
checks 1,151 modules / 7,975 declarations with zero reuse. See
[the current closure status](CLOSURE_STATUS.md), [the final theorem map](FINAL_THEOREM_MAP.md)
and [the Palomar audit](PALOMAR_AUDIT.md). Actual public-commit/native CI and
Palomar acceptance remain open. The dated development descriptions below are
historical and do not reopen completed mathematical dependencies.


Date: 2026-10-05. Source audit and finite native evidence; the universal Lean
byte/CPU refinement theorem is **pending**.

The [official Intel catalogue](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
listed SDM revision 093, updated 2026-09-21. The downloaded
[Volume 2A](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf),
[Volume 2B](https://cdrdv2-public.intel.com/929354/253667-093-sdm-vol-2b.pdf),
[Volume 2D](https://cdrdv2-public.intel.com/929356/334569-093-sdm-vol-2d.pdf) and
[Volume 3A](https://cdrdv2-public.intel.com/929359/253668-093-sdm-vol-3a.pdf)
are pinned by SHA256 in [intel-manuals.json](../validation/intel-manuals.json).
The earlier 2016 manual remains historical evidence only.

The relevant ISA forms are memory XCHG, accumulator-to-memory MOV/MOFFS,
memory-destination ADD/SUB/SBB/XOR/AND, SP exchange/store and near CALL.
CALL's pushed next instruction pointer is included in the construction;
its target is obtained before that return-field overwrite. CET shadow-stack
writes require additional architectural state, so the tested fixture requires
shadow stacks disabled and checks that process setting. These contracts are
reviewed from the complete selected instruction entries. G63 checks their
selected sequential effect projection; full compiler/CPU realization remains open.

G58-G61 now check the selected codec and byte-memory/layout layer in
`Native/LittleEndian`, `Native/Encoding`, `Native/ByteMemory` and `Native/Layout`.
The codec distinguishes x86 `A3` stores, x64 fixed `48 89 05` stores and owned
`48 A3` fields. Indirect CALL uses `FF 15` without REX.W. Full-width MOFFS
payloads and four-byte displacement payloads have exact round trips and slices;
all selected instruction lengths are at most 15 bytes. Byte patches preserve
surrounding bytes, sequential fetch reads the new MOFFS address, and the affine
grid has checked ownership, alignment, disjointness and finite capacity bounds.
Byte positions here are natural numbers; these results alone do not establish
signed RIP relocation, canonical x64 pointers or CPU execution/fetch semantics.

Volume 3A sections 11.1.3 and 14.6 discuss self-modifying instruction fetch.
The former specifies a store followed by a control transfer before executing
changed code, or a serializing operation. The latter discusses same-linear-address
coherence and older processor differences. CALL is not asserted to be a serializing
instruction. The proposed realization requires coherent current-word fetch for
the temporary DEFADDR patches and the CALL control transfers before later use of
updated operands. Proving that complete discipline sufficient for a named CPU
configuration remains a refinement obligation.

The native fixture uses one thread and one mapping for stores/fetches, writable
executable image code, aligned full-width fields, valid near displacements,
representable pointers, canonical x64 addresses and a finite initialized interior.
Host cache flushing occurs before entry, outside the pure computation. No
concurrent patching, arbitrary CPU support or fixed-width infinite tape is claimed.

[generate_pure.py](../validation/generate_pure.py) emits shared readers whose
unique MOFFS operand owns each active label; the dynamic store enters that same
instruction. Padding precedes called entries or lies in unfetched storage templates.
The thirteen logical registers and two words of each heap cell occupy one affine
grid, with spacing 8/16 bytes on x86/x64. Linked runtime checks verify each field's
opcode bytes, alignment and non-overlap. Every CALL resets SP so its return store
lands in one code operand; no growing ordinary stack is used within the kernel.

[pure.json](../validation/pure.json) records the current processor, compiler
commands, source/audit hashes, linked assembly/disassembly hashes and native tests.
Both architectures pass 109 cases, 535 observed body passes and 107 genuine
closed-loop runs. The host entry and terminal stubs perform setup/observation
outside the computational purity boundary. Tests compare complete logical
register/heap effects; their expected TM answers are never initialized into the
computational state. This finite evidence supplements the checked word-model
construction, simulation, code-change and effective-execution proofs. Formal
selected byte encoding, patch/fetch and layout proofs are checked; CPU execution
and hardware fetch refinement remain pending.

## Checked allocation and effective permissions (N56-N58)

`Native/AddressSpace` checks complete byte windows using allocation endpoints.
Flat x86 requires an upper endpoint at most `2^32`. For configured four-level
or five-level x64 paging, the allocation lies wholly below `2^47` / `2^56`, or
wholly in the corresponding high canonical interval ending at `2^64`.
The canonical hole is rejected. The configuration is a parameter; five-level
support is not inferred for every CPU. These are ordinary unmasked addresses;
LAM is outside this model. The definition follows the paging-canonical rule in
[SDM Volume 3A, section 4.5](https://cdrdv2-public.intel.com/929359/253668-093-sdm-vol-3a.pdf)
(PDF page 108 of the SHA256-pinned copy). The selected CALL instruction-pointer loads require paging-canonical targets
(section 4.5.2). Memory-window validity alone does not discharge that target check.

`Native/MappedExecution` adds effective read/write/execute permission bits to
the finite evaluator. Its current-byte classifier chooses the form; it checks
all three header bytes, the complete classified packet, any selected data-read
word and the complete write word, including CALL's decremented-SP slot.
A static valid RWX allocation certificate derives these checks at every actual
successive state. `ProgramMapped.kernel_checked` and `closed_checked` apply it
to the actual emitter/kernel/backedge and retain exact source outcomes, every
represented register/heap word, owned writes and the closed entry PC. No future
trace or dynamic pointer certificate is an environmental premise.

The checked windows describe memory accesses and fetches, not every ISA fault
condition. In particular, a CALL validates its target when loading the instruction
pointer. A trace can end at that target without fetching there; containment of
the preceding instruction and stack write therefore does not prove its target
canonical. The endpoint may be a host observation target; the general
`Request` type itself does not constrain `terminalOffset` to `hostSpan`. N59-N60 now prove every CALL target of an accepted closed pass address-valid:
interior targets are followed by contained fetches, and the final backedge returns
to the contained initial entry. `ProgramControl.closed_checked` retains this
property along with all checked memory windows and full output/ownership. N61-N64 now derive the rejected source/host endpoint from literal layout and
frozen target values, with the explicit premise `terminalOffset < hostSpan`.
The combined evaluator checks CALL target validity as well as all memory windows.

These effective permission bits are not a verified page-table implementation.
They must describe the actual stable mapping and applicable protection rules.
Flat x86 CS/DS/SS translation, the selected nonfaulting ISA projection, relevant
configuration (including CET disabled), single-thread/current-mapping execution
and coherent fetch of changed instruction operands remain physical realization
conditions. The model rejects an invalid PC or missing execute permission;
such a rejection is not an intended source-machine halt. Host mapping setup,
cache flushing and endpoint observation remain outside the pure computation.

## Combined checked finite execution (N61-N64)

`ProgramEndpoint` transfers the original terminal-field value through the frozen
frame invariant, then derives the final PC by actual source-schedule induction.
`SourceEndpoint.kernel_pc` identifies accepted progress with the computed backedge
and rejection with the initialized host/trap target. The explicit condition
`terminalOffset < hostSpan` puts that target inside the fixed allocation, and
capacity proves the encoded address does not wrap. Configured canonical geometry
therefore applies to every actual direct/indirect CALL, including an unfetched
rejected endpoint. The MASM comparison checks this exact host-span condition;
the fixture has offsets/spans 9/21 on x86 and 10/23 on x64.

`CheckedExecution.step` combines live-byte fetch, contained fetch/read/full-word
write windows, effective RWX permissions and actual CALL target checks in one
partial finite evaluator. Loaded-byte agreement preserves the indirect target
read before the CALL push. A rejected target produces evaluator failure, not an
intended source halt. `SourceChecked.kernel` and `SourceChecked.closed` construct
accepted checked traces for the actual initialized kernel and body/backedge,
preserving exact source outcomes, every finite source word, code-owned writes
and the precise final PC. All later target/access/Ready facts are derived.

This closes the modeled canonical/permission/target application. Actual stable
mapping and effective protection rules, flat segments, selected ISA projection,
CET-disabled execution and coherent current-byte instruction fetch remain the
physical refinement conditions described above. No entire CPU/OS implementation
or physical resource-unbounded execution is claimed.

## Continuous repeated-pass execution (N65-N67)

`ProgramIteration.run` passes the actual resulting source and native state from
each accepted body/backedge to the next iteration; it stops at the first rejected
source pass. The original memory snapshot stays fixed for the whole proof.
`Bounded` describes only the successive literal source-kernel runs, not later
native safety, targets or readiness. The source invariant transfers frozen
metadata, intact opcode bytes and the selected heap pointer at every boundary.
`LoopBounds.pass_safe` derives each subsequent access bound from that invariant
and static allocation geometry.

`SourceIteration.checked` instantiates this induction with the actual emitter,
original initializer, computed kernel/backedge and host endpoint. One continuous
finite checked trace preserves exact source outcomes, every represented register
and heap word, code-owned writes, all modeled checks and the exact final PC.
Every accepted pass contributes its three actual backedge events, giving at least
`3 * count` events. No byte image or source values are reinitialized between passes.

Capacity/compactness, positive source cells, closed backedge, the source path's
word/cell bounds, static effective mapping and host-span condition remain explicit.
This establishes bounded repeated execution in the selected model; physical
ISA/configuration/current-fetch refinement and literal printed-source obligations
remain separate. It does not identify fixed-width memory with an infinite tape.

## Selected-form assembler conformance

`validation/audit_encoding.py` exports 26 zero-payload shapes from the checked
Lean codec and compares the computational instruction headers with MASM's
COFF object bytes. It checks raw MOFFS owners, complete operand-field alignment
and disjointness, the register/heap grid, relocation placement/type, resolved
direct CALL destinations, and separately recorded alignment padding. Listing
offsets are interpreted within their section; the host descriptor data section
is excluded.

The current finite fixture audit passes: x86: 1916 headers, 8243 fields, 1412 relocations; x64: 1916 headers, 8243 fields, 1412 relocations.

The report records source/object/listing hashes and ties the fixtures to the
current Lean and native reports. x64 SBB uses `REL32_1` because its immediate
follows the displacement; x64 MOFFS uses `ADDR64` and ordinary RIP-relative
forms use `REL32`. The relocation reference is Microsoft's
[PE/COFF specification](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format#type-indicators).
This is finite assembler conformance evidence. It does not prove the Python
generator correct for all inputs, CPU instruction semantics, whole-program padding
unreachability or hardware self-modifying fetch coherence.

See [encoding.json](../validation/encoding.json).

G62 (`Native/Arithmetic`) checks the adopted unsigned borrow and SBB-value
equations at 32/64 bits: zero minus an incoming borrow is all ones, and
XOR/AND/XOR selects either complete target word. Both tag guards accept/reject
encoded heap addresses and Boolean offsets as intended under representability
bounds. Indexed whole-word addition produces the selected adjacent heap field,
and an explicit bound yields its exact natural address without wrap. This is
composed with the selected sequential execution/CF projection in G63-G64;
whole emitted-role/source-block refinement remains open. The SBB reference is pinned Volume 2B, section 4-613/4-614.

G63 (`Native/Execution`) specifies the selected sequential, non-faulting
flat-segment instruction effects on IP, accumulator, SP, CF and unified byte
memory. It uses absolute disp32 in x86, full-next-IP-relative signed disp32 in
x64, and sign-extended rel32 near CALL. Ordinary MOV and XCHG preserve CF;
near CALL preserves it without a task switch. XOR/AND clear CF, and SUB/SBB
use unsigned borrow. Other flags are outside this observed projection.

Kernel-checked decoded traces preserve CF across ordinary MOV/XCHG/near-CALL
bridges, and the subsequent SBB mask consumes the earlier SUB borrow. CALL
loads its indirect target before overwriting an aliased return slot, stores the
complete next IP at decremented SP and preserves the accumulator. A patched
MOFFS packet executes with its newly fetched address. G64 adds opcode-derived automatic packet
fetch. These contracts do not yet establish the complete generated source/compiler
simulation or hardware instruction fetch.

The execution environment must also disable CET indirect-branch tracking for
these targets, which have no ENDBR prologues. The native fixture explicitly
checks shadow-stack policy; it does not independently record an IBT policy
query. Permissions, valid segments, canonical addresses, capacity and coherent
instruction fetch remain explicit realization conditions. Ordinary MOV is
reviewed separately from control/debug-register MOV, whose flag rules differ.
The reference extractor now includes complete ordinary instruction entries
from Volumes 2A, 2B and 2D; downloaded source evidence is not an ISA proof.

## Automatic fetch and repaired reader byte contract

G64 (`Native/Fetch`) classifies the selected length from at most three live
opcode/ModR/M bytes, with no supplied form or length. The exact decoder then
reads the current complete packet and validates its payload, including SBB's
imm8 zero. Encoded lengths are independent of trailing instruction bytes and
address values. The proof uses a 15-byte window only to establish a prefix;
the defined fetch classifier reads a three-byte header. Automatically fetched
MOV/XCHG/near-CALL traces preserve CF, and the subsequent zero SBB mask consumes
the original SUB borrow. Patched MOFFS addresses are fetched and executed live.

G65 (`Native/Writes`, `Native/Reader`) proves the full byte store and outside
frame for every selected operation, including CALL's return slot. Rewriting a
loaded word restores every byte. The repaired reader's first two operations
restore the label; its final two restore the target. Its complete memory
function is unchanged at the end, the accumulator contains the double load,
and SP/CF are preserved. All four writes are complete nonempty word writes to
the label or loaded pointer field whenever those fields are owned.

The G65 local contract takes the first three current packets and their
resolved label addresses as premises. G71 below discharges those premises for
a constructed reader fragment. The final MOFFS fetch is proved from its current
encoding when the target equals the label, or when the target word is disjoint
from the entire final packet. Arbitrary partial byte overlap is not declared
safe. The prefix lengths are 13/17 bytes and the label offsets 14/19 bytes for
x86/x64, matching MASM. G66-G67 compose code-backed SP reset/return and the
complete reader callee below. Full placement, guard/source-block composition,
relocation/canonical/capacity bounds and coherent hardware fetch remain open. Natural byte memory is the specified
sequential projection; no unbounded physical x86/x64 memory is asserted.

## Reusable code-backed calls and complete reader callee

G66 (`Native/Calls`) checks the two SP-reset instructions and either selected
near-CALL form in both modes. The reset restores all StackTop bytes for any
incoming SP, sets SP from the StackTop word and preserves accumulator/CF.
When StackTop contains ReturnField plus the word width, the subsequent push
lands exactly at ReturnField. The transfer target is evaluated before that
push; an indirect return through the same field jumps to its old value while
replacing it with the complete next IP. Every other byte is framed.

When the StackTop word and ReturnField have separate byte footprints, the
StackTop constant survives the CALL and is available to the next reset. All
three write destinations are owned if those two fields are owned. The reset
occupies 12/14 bytes in x86/x64; including relative CALL it occupies 17/19 bytes,
or 18/20 bytes with indirect CALL. These contracts hold for actual automatic
packet traces under the stated operand-address and initialized-value premises.

G67 (`Native/ReadCallee`) composes the four-instruction reader with reset and
indirect return. The seven-instruction body occupies 36/47 bytes, excluding
padding before its entry. Its complete result returns the double load in the
accumulator, preserves CF, leaves SP at ReturnField, jumps to the old return
target and restores every byte except that field. The resulting field contains
the callee return CALL's next IP. All seven writes are owned under the declared
label/pointer/top/slot ownership premises. Actual fetch traces and the owned
write property compose at the intermediate reached state.

A direct caller followed by this callee returns to the caller's complete next
IP. The two return-slot writes reduce to the callee's final return word; other
caller bytes are restored, and CF is preserved across the round trip. These
are local selected-ISA byte contracts. The full placed image must still prove
live opcode/operand preservation, resolved relocations and owned-field premises;
guard/source-block/compiler composition and hardware validity/fetch remain
required. CET-disabled and non-faulting flat-segment assumptions still apply.

## Concrete byte storage grid and protected opcodes

G68 (`Native/Protected`, `Native/GridImage`) constructs the repeating storage
layout: x86 A3 or x64 48 A3 opcode, the whole 4/8-byte word operand, and padding
to the 8/16-byte grid stride. The initializer is an explicit byte function;
provided word values are encoded exactly and every owner opcode is established
from that function. No initial header or fetch oracle is a premise of these
storage-grid results.

A protected MOFFS prefix plus arbitrary current operand bytes forms an exact
selected encoding. Automatic fetch decodes that current word, independently
of any initial/cached payload. Grid word stores are proved disjoint from every
owner prefix, including the written field's own prefix. The invariant survives
individual selected instruction effects and complete actual owned-write traces.
Natural-address loads agree with encoded CPU-address loads under an explicit
representability bound; wrapping is not silently ignored.

These results cover the register/heap storage grid. G69-G70 below construct and
protect finite control/metadata fragments over this grid. Whole generated-kernel
role placement, finite-data compiler initialization and guard/source-block
alignment still require proofs.
Byte addresses are natural numbers in the sequential projection. Physical
finite-prefix use additionally requires capacity, canonical/segment/permission
and coherent hardware fetch conditions; the infinite byte function does not
claim an infinite physical x86/x64 address space.


## Constructed control images and placed reader

G69 (`Native/ControlImage`, `Native/ControlPacking`) initializes finite packets
from their actual encodings and computes adjacent byte positions. Fixed packets
include immutable address/displacement bytes; owned packets permit changes only
to their MOFFS address word. Computed extents establish byte separation. Owned
stores preserve each fixed packet and every owned opcode. Initialization frames
all backing bytes outside the fragment.

G70 (`Native/CombinedImage`) overlays that finite fragment on the initialized
storage grid under a checked extent gap. Every initial grid word survives the
overlay. Control-owned and grid-owned stores preserve both regions, including
on actual automatic-fetch traces. An owned address identifies a real current
MOFFS operand with a decodable owner, rather than an arbitrary write predicate.
These generic constructors do not yet instantiate the entire MASM kernel layout.

G71 (`Native/ReaderImage`) constructs the four repaired reader packets, their
positions and the final mutable label. The x86 exchange uses its computed
absolute label address; x64 uses RIP offsets 12 and 5. All four current-byte
fetches follow from the initialized image and its invariant, with explicit
capacity, region separation and loaded-pointer grid ownership. No supplied
fetch or packet-length premise remains for this fragment. Every instruction
writes an owned code field. The complete byte memory, SP and CF are restored,
the accumulator receives the exact initialized grid value, and the ending IP
is the fragment's computed end. G75 below composes the seven-instruction callee. G76-G78 below compose the read/store caller round trips. Guards,
guards, source blocks and compiler composition remain required.

## Computed relocation contracts

G72 (`Native/Relocation`) represents rel32 as the signed target-minus-complete-
next-IP difference. The explicit range is [-2^31, 2^31). Its 64-bit sign extension
and target sum are checked for forward and backward transfers in both modes.
x86 absolute disp32 and x64 RIP-relative disp32 resolve to computed word targets.
Resolution uses each complete instruction length, including SBB's imm8 zero,
covering the distinct REL32_1 position. Relative CALL reaches its computed word
target; a separate capacity bound gives equality to the natural byte position.

These word laws do not assert that arbitrary relocation values fit or addresses
are canonical. The full emitted image must establish the range/storage bounds,
valid segments and permissions, CET conditions and hardware fetch discipline.
The sequential projection and successful native fixtures do not by themselves
prove that hardware always fetches restored or modified operands coherently.


## Whole-image fragment views and constructed callee

G73 (`Native/Fragment`, `Native/ReaderView`) proves prefix/suffix placement
embeddings and exact operand initialization from the finite encoded packets.
The reader's pointer can refer to another reader, scalar metadata, grid storage
or its own label. Actual whole-image ownership and separation establish either
exact self-alias or disjointness from the last packet. No independent fetch or
byte-overlap premise is needed. Distinct owned field addresses are proved
byte-disjoint across both control and grid regions.

G74 (`Native/CallsImage`) constructs the reset and either near-CALL packet,
computes their absolute/RIP/relative displacements and derives all three current
fetches within the whole image. The required signed displacement ranges and
body capacity remain explicit. StackTop's slot-plus-width value places the push
at the owned return operand. Relative and indirect transfer targets are derived
from the computed operands and pre-push memory.

G75 (`Native/ReadCalleeImage`) constructs the 36/47-byte seven-instruction body.
Reader and call fragment embeddings compose into a view of the whole image.
Every fetch and resolved-address premise of the local callee contract is derived;
its owned writes preserve all control and storage opcodes. The return reads the
old slot target and then stores the computed callee end IP into that slot. All
other bytes are restored; accumulator, SP and CF results are exact. Distinct
owned StackTop and return operands establish the reusable StackTop frame.

The initialized variants recover the pointer and StackTop value from actual
finite operand encodings, with no initial load-equation premise. They still
require finite role membership, data ownership, extent/capacity and displacement
bounds. These results are composable callee contracts, not a completed proof of
the entire emitted MASM kernel. G76-G78 below compose the read/store caller
round trips. Guards, source blocks, global alignment/role layout and finite-data compiler simulation
remain open, together with hardware validity and coherent fetch conditions.

G76 proves the full ten-instruction placed read invocation, including the
return-field alias and complete memory restoration except for the final return
word. G77 constructs the four-instruction store callee at the same mutable
MOFFS instruction used by the reader. G78 proves the seven-instruction placed
store invocation, its computed return position and exact destination/return
writes. Byte-store commutation removes the caller's intermediate push from the
final memory equation. Both invocations preserve CF, reusable StackTop and the
whole image; the store also preserves AX. Ownership derives byte separation,
with the store destination distinct from StackTop and the return field.

The store invocation explicitly requires its destination to differ from
StackTop and the return field. Its label survives the caller's push because it
is a distinct owned field; subsequent destination/return stores commute by
derived full-byte separation. These are finite image and state preconditions,
not supplied fetch or execution premises. Their instantiation for the whole
kernel remains part of the guard/source/compiler and role-layout obligations.

G79 computes finite packet placement with explicit padding, derives separation
and exact byte initialization, and embeds contiguous bodies in the padded
sequence. G80 preserves the complete padded control/grid image through owned
writes; uncovered bytes before the grid initialize to 90h. The global fragment,
reader, reset/CALL, callee and read/store invocation contracts now use this
context. G81 checks the generator's ALIGN formulas: 2/5 extra bytes for reader
labels and 3/6 for scalar owners on x86/x64, with no-wrap lifting to aligned
encoded field addresses. Whole emitted role-layout instantiation remains open.

The original G69-G70 adjacent constructor remains a checked special case: G80
proves equal byte images and equal ownership/invariant predicates for zero
padding. The current unit contracts accept computed padded finite pieces,
with local contiguous bodies embedded through finite entry membership. Padding
is outside the selected instruction list; it is not encoded as a computational
NOP. The complete generator role AST and proof that every whole-kernel transfer
uses its computed entries are still required, along with applied address bounds,
guard/source semantics and hardware fetch discipline.

G82 constructs the fixed MOV/ADD/SUB/XOR/AND/SBB memory-destination packets,
with computed complete-size displacements, derived automatic fetch and owned
writes, exact modular values/CF, AX/SP preservation and byte/word frames.
G83 composes the guard's actual 13-instruction SUB/read-zero/MOV/SBB sequence.
The reader and mask initialization preserve the original SUB borrow; SBB emits
its exact zero/all-ones mask. Intermediate readiness is derived from the finite
image/state setup and field separation. Only scratch, return and mask words
remain changed; StackTop and distinct zero/reader metadata are reusable. The
complete guard composition is checked by G87-G88.

G84 composes the actual 26-instruction capture/setup prefix: the inline reader
captures the original caller return word before nested CALLs overwrite Slot;
fixed MOV saves it in Resume, the candidate reader loads the original candidate,
MOV saves it in Scratch, and the boundary reader leaves the original boundary in
AX. All current-byte fetches and owned writes, exact ordered memory effects,
AX/SP/CF, reusable StackTop/image/boundary metadata and byte/word frames are
checked. Intermediate readiness follows from proof-only initial-memory views,
computed positions, the preserved image and derived owned-field frames.
Fixed accumulator MOV matches MASM's five-byte A3 in x86 and seven-byte
RIP-relative 89 in x64; scalar and borrow-mask contracts are rechecked with
these actual lengths. The selection/return stage is checked by G86; G87-G88 compose the complete guard.

G85 checks the eleven-instruction complete read/update pair: the placed
reader round trip followed by a computed fixed MOV/ADD/SUB/XOR/AND/SBB.
Readiness, current-byte fetch, owned writes, exact source/target/CF/AX/SP and
two-field memory effects, byte/word frames and reusable image/StackTop follow
from the initial setup. G86 composes four such pairs and the reset/indirect
CALL into the actual 47-instruction selector. XOR/AND/XOR computes the exact
full-word mask selection; a zero/all-ones mask chooses continuation/terminal.
The CALL uses the selected target before its return-slot write. Final memory
has exactly Selected and the computed caller-end return word; all intermediate
reader return words and selector writes are overwritten. CF is false, AX is
the continuation value, SP is Slot, and image/StackTop and other distinct
owned fields are preserved. Readiness transfers through the image and derived
stack-top/three-reader-label frames, without assuming an executed bridge or
chosen target.

G87 composes the actual setup, borrow-mask and selector into the complete
86-instruction native guard. Original-memory setup and injective physical
metadata roles derive every executed readiness and preserve reader labels,
StackTop, zero, saved Resume and Terminal through the actual writes. The borrow
uses the original candidate/boundary; Base faults on borrow and otherwise
resumes, while Offset reverses these targets. Exact ordered memory, current-byte
fetch, owned writes, CF/AX/SP, selected/Slot words and reusable image/frames are
checked. G88 adds the actual three-instruction reset/relative-CALL, derives
post-call readiness through owned-field separation, and proves the complete
89-instruction round trip reaches its computed outer caller end or the original
terminal word. No executed bridge, mask, return value or selected target is
supplied. These additions contribute 60 audited declarations. Whole emitted
role-layout instantiation and source/compiler/hardware realization remain open.

G89 connects the native encoding to Dolan's actual tagged source words:
addresses become first-half heap pointers and offsets become 0/stride. Under
no-wrap bounds, the encoding is injective and the complete caller guard performs
the source tag test. The Base guard also classifies the computed pointer:
offset-plus-offset remains below the heap boundary, while address-plus-offset
selects the correct adjacent field. G90 constructs the bounded source register/
heap representation and initializer, with all thirteen registers and both
fields of every represented heap cell, derived ownership, separation and fits.
G91 proves the actual eleven-instruction immediate block implements the literal
source MOV, updates the intended source register and preserves every other
register and every represented heap word. The native trace, owned writes,
exact memory and CF/AX/SP, next PC and reusable image/StackTop are checked.
These additions contribute 42 audited declarations. Complete 233/239-instruction
load/store refinement, emitted role/compiler instantiation, applied bounds and
hardware region/fetch assumptions remain open.

G92 composes the actual source offset reader/Candidate store and the complete
caller guard into the 100-instruction offset-check prefix. Metadata ownership,
physical separation and exact Candidate/Slot frames derive the executed guard
setup; the candidate is read from the original represented source register.
The prefix accepts exactly source offsets and chooses the computed continuation
or original failure word under the stated source-cell/no-wrap bounds. All source
registers and represented heap words are preserved. Its current-byte trace,
only code-owned writes, exact outside-six-field byte frames, CF/AX/SP and
selected/Slot words and reusable image/StackTop are checked. These additions
contribute 30 audited declarations. Remaining whole role/compiler
instantiation and hardware region/fetch refinement remain open.

G83's initial reader setup is a proof-only view of the original memory at the
computed reader-call PC. The actual post-SUB reader readiness is derived through
opcode preservation and owned-field byte frames. The bridge trace, zero load
and borrowed CF are not assumed. MOV and SBB readiness then follow from the
reader's computed return position and preserved image. The exact memory
contract removes the intermediate zero store and retains the ordered SUB,
return-word and final mask writes, even for permitted aliases between those
fields. Separate zero/reader reuse statements require their fields to differ
from the mask. Whole emitted-role/source composition and hardware realization remain
open.

G93 checks the 33-instruction pointer construction: the base and offset are read from represented source registers, added in the single active load/store operand, then copied through the PointerWord reader into Candidate. Source-register aliases are allowed; all represented data and other owned metadata are preserved. G94 composes both guards and this pointer stage from original-memory setup. A malformed offset stops after 100 instructions; a valid offset reaches the Base guard after 222. The continuation is chosen exactly when the literal source address succeeds, and its selected heap word is left in the shared operand. Current-byte traces, code-owned writes, frames for other owned words outside the seven written fields, source-data preservation and reusable image/StackTop/SP/CF are checked. Remaining emitted role/compiler instantiation, applied bounds and hardware region/fetch refinement remain open.

G95-G96 check the complete native source load and store blocks. Both derive later reader/store setup from the executed guarded address stage and original static placement. The computed pointer is the single active operand shared by load and store. A successful load performs the literal source register update while preserving every other register and heap word; a successful store updates precisely the selected heap word and preserves all registers and other represented heap words. Source register names may alias. Malformed offsets stop after 100 instructions, malformed bases after 222, successful loads after 233 and stores after 239. Exact source outcomes, complete represented-state effects, current-byte traces, code-owned writes, owned-word frames and reusable image/StackTop/SP/CF are checked under explicit cell/no-wrap bounds. N18-N22 close whole emitted role/compiler instantiation under explicit capacity/compactness and source-path bounds. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

Validation uses lakefile.proof.toml with .lake/proof-build, separate from the editor cache. validation/lean_build.py checks that this Lake configuration differs from the canonical lakefile.toml only in buildDir; the package, Lean options, targets and dependency pins are identical. All Lean/native/encoding launchers use that configuration, and both configurations plus the shared launcher and proof audit script are hashed in the evidence. This avoids replacing editor-mapped Windows .olean.private files.

G97-G99 check native program composition, the actual backedge, and lowering of the exact exported 64-MOV kernel. Block readiness is derived from one initial metadata snapshot, physical field separation, the intact image and the actual selected heap pointer; no later trace or Ready is assumed. Finite schedules stop at the literal source trap and preserve all represented source data and code ownership. Successful schedules reach the computed end PC with a reusable invariant; the reset/indirect CALL composes into a closed pass. The kernel layout pass preserves all 64 instruction operands, a common source grid and contiguous encoded PCs. Its address-immediate rejection is explicit: the fixed kernel uses only offset immediates. N18-N22 now derive the complete static placement/metadata certificate from the padded emitter image and prove its full bounded/closed byte pass. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N00-N01 construct the literal inline packet sequences for all source blocks and both shared guards. The exact exported kernel has 1,678 source-body packets, and each guard has 37 inline packets. Physical source/guard positions, finer reader-caller/scalar-entry placement and whole-body embeddings in the padded image are derived from the packet builders. For compiled source schedules, explicit static end-position bounds discharge the conversion from encoded continuations to natural byte positions. N02-N08 now construct that aligned prefix, resolve its addresses and initialize all roles in the complete emitted byte image. N09-N17 derive context consistency, initial reader/scalar readiness, both complete guard certificates, the initial loop invariant and backedge setup. N18-N22 derive every compiled source block's initial Ready, immutable-role frames and the full source-schedule certificate. N23-N27 now construct finite loaded-prefix equivalence. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N02-N08 add 50 checked declarations for aligned templates and finite pools, literal role initialization, native byte lengths, affine metadata separation, the two-pass address allocator and complete byte-image initialization. The exact kernel occupies 9,382 bytes in x86 and 10,816 in x64; guards occupy 206 and 244 bytes. The constructed image contains all 23 shared readers, both guards, source body, backedge and 13 metadata owners; the host observation gap remains unfetched backing bytes. All reader and metadata operands have computed initial values, ownership and alignment, and represented source words initialize correctly in the protected data grid. N09-N17 prove that the source reference context equals this constructed whole and derive the guard and backedge certificates. N18-N22 derive every source block's initial Ready and the full source-schedule Setup. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. `ExportLayout.lean` supplies the allocator's coordinates for an independent finite MASM comparison; that comparison is evidence, not a proof of the Python generator or hardware semantics.


N09-N17 add 76 checked declarations. The fixed compilation now constructs a self-consistent complete byte image; all 23 reader and 13 metadata fit conditions follow from one finite source-grid capacity bound. Metadata fields, reader operands and both guard captures have injective physical and encoded addresses. Literal placed bytes and initialized operands derive reader/scalar/read-update readiness, both complete guard orientations, the initial represented/intact/frame/selected invariant and backedge Setup. Fixed control/register relocations use the explicit compactness condition `heapBase - origin < 2^31`; heap MOFFS operands use full-width capacity bounds. N18-N22 derive its frames across every compiled source block and each block's initial Ready, closing every field of `ProgramImage.Setup`. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. Overall completion remains incomplete.


N18-N22 add 38 checked declarations and close the whole emitted source-schedule certificate. Each block has an actual lowerer witness; its static observations belong to the constructed immutable role set, and that set is disjoint from its complete final-write destinations. All immediate/load/store initial Ready predicates follow from literal placed packets and initialized bytes, with source-register aliasing permitted. `ProgramCertificate.source_setup` supplies every field of `ProgramImage.Setup`; exact entry/end/Linked PCs and a full current-byte/code-owned bounded kernel pass are proved. `closed_pass_correct` composes an accepted pass with the actual backedge and restores the full invariant at kernel entry. Capacity, `heapBase - origin < 2^31`, positive cells and the path's source-address bounds remain explicit. N23-N27 construct finite loaded execution. N43-N55 close the allocation extent bounds. Physical mapping/canonical conditions, coherent hardware fetch, remaining source/appendix proofs and registry packaging remain open. Overall completion remains incomplete.

N23-N27 add 44 checked declarations for finite loaded-memory refinement. A finite byte image stores exactly the loaded interval; its partial evaluator automatically fetches current bytes and accepts only contained header/packet, data-read and full-word-write windows. Loaded-byte agreement preserves all selected scalar effects, write addresses/values, traces and ownership while framing exterior bytes. A computed containing interval supplies safety for every finite fetched prefix without assuming a safe execution. The whole emitted kernel and accepted body plus actual CALL backedge now have constructed finite loaded executions with literal source outcomes and every represented register/heap word preserved. The extent includes the complete represented finite grid. N43-N55 close containment in the prescribed allocation. Physical mapping/canonical conditions, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N28-N35 add 38 checked declarations for bounds in one allocation fixed by the emitted layout and requested finite source grid. Every placed control entry has a contained fifteen-byte fetch window; complete metadata, register, selected heap and all 23 initial reader-pointer words are contained, and the allocation fits the finite machine address space. Initial pointer/StackTop values and actual executed-state frames derive bounds for the repaired reader, reset/CALL, seven-instruction callee, ten-instruction caller round trip, each scalar operation and eleven-instruction read/update. Literal initialized placed callers and read/update fragments therefore have finite loaded executions in this prescribed allocation. N36-N42 compose the guards; N43-N55 complete the dynamic source and whole-kernel allocation certificate. Canonical-address validity, permissions/segmentation/CET, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N36-N42 add 22 checked declarations composing the fixed-allocation bounds through all guard stages. Static packet placement derives reader/callee/scalar/CALL fetch windows from one control interval. Proved pointer frames derive every data-read and complete word-write bound through the 26-instruction capture/setup, 13-instruction borrow-mask and 47-instruction selector/return stages. Both 86-instruction guard orientations and the actual 89-instruction outer invocation have finite loaded executions in the preselected allocation, derived from the initialized emitter image, capacity/compactness and typed metadata; no future safe trace or intermediate Ready is supplied. N35 additionally proves containment of the whole static control interval, bringing its declaration count to 19. N43-N55 close the remaining dynamic source and whole-kernel allocation bounds. Physical canonical/permission/segment/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.

N43-N55 add 31 checked declarations closing dynamic source and whole-kernel bounds in the allocation fixed before execution. Pointer construction reads contained register and operand words without dereferencing an unvalidated value. Successful load/store operands are proved equal to the selected contained heap word from source representation and finite-cell bounds; rejected tag paths execute their contained guards. All actual compiled blocks obtain static certificates from their literal lowerer witnesses. Schedule induction derives current Ready from the preserved invariant at every boundary, then composes the complete emitted body and actual reset/indirect CALL backedge. `ProgramAllocation.kernel_loaded` and `closed_loaded` construct their finite loaded executions with exact source outcomes, every represented register/heap word, code-owned writes and the closed entry PC. No future safe trace, intermediate Ready or trace-dependent allocation extent is supplied. Address-space capacity, compact relocations, positive cells and source-path cell bounds remain explicit. Physical mapping, canonical/segment/permission/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.

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
