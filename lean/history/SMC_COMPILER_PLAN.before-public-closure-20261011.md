# Pure SMC compiler implementation plan

## Current acceptance — 2026-10-11

Mathematical proofs and conditional native/head/COFF bindings are complete;
rounds 1–6 are accepted at immutable passing checkpoints. The final cold replay
checks 1,151 modules / 7,975 declarations with zero reuse. See
[the current closure status](CLOSURE_STATUS.md), [the final theorem map](FINAL_THEOREM_MAP.md)
and [the Palomar audit](PALOMAR_AUDIT.md). Actual public-commit/native CI and
Palomar acceptance remain open. The dated development descriptions below are
historical and do not reopen completed mathematical dependencies.


Date: 2026-10-05. Status: complete guarded compiler and computation theorem
checked in the unbounded word model; complete finite native implementation
tested. Byte/CPU refinement and the remaining full-scope gates are pending.
This continues the complete objective in [PROOF_LEDGER.md](PROOF_LEDGER.md).

## Checked foundation and chosen backend

`Dolan/Simulation.fixed_mov_simulation` proves the fixed 64-MOV kernel's
simulation, bounded scanner progress, halting and divergence for arbitrary
finite TMs. `FourSimulation.four_register_mov_simulation` independently proves
the requested four-register Dolan foundation using a fixed 2,252-MOV body.
Both results remain part of the project.

The SMC backend lowers the 64-MOV logical kernel directly: its thirteen logical
registers are instruction operands, with accumulator/SP hardware scratch.
This avoids multiplying the SMC body by the four-register ring-walk expansion
and retains the same intended pure two-hardware-register computation result.
`ExportKernel.lean` exports the checked program for native generation.

`LoweringCorrect` checks the earlier successful effect compiler. `Guard` checks
the 39-instruction inline guard algebra and code writes. Shared routines now
have actual fetched 10/11/7-instruction read/copy/store proofs. `ConcreteImage`
now constructs the unbounded word image, proves all storage owners and shared
reader placement; `ConcreteCalls` discharges the static read-call contracts.
`VirtualInstructions` checks source effect tails under valid-pointer hypotheses.
`VirtualInitialization.data_state_correct` initializes represented data by
arithmetic field lookup. `ConcreteInitialization` and `ConcreteTMInitialization`
now initialize all metadata and compose with the finite-table/blank-tape source
initializer. The fixed image and initial words use no future-execution answers.

## Operand ownership and layout

Use shared routines. Each active read label occurs in exactly one MOFFS operand.
A reader executes corrected DEFADDR, resets SP and CALLs through a common
code-backed return field. A store enters the same reader's final MOFFS instruction.
This resolves the duplicated-operand problem in the inline effect compiler.

Keep active labels, constants, selected targets, address scratch and return
storage separate from the uniform data grid. The grid holds thirteen logical
register words and two words per heap cell. Addresses encode the first word's
field address; offsets encode zero or the field spacing. Injectivity, register/
heap separation and metadata frames are checked. `ConcreteImage` now gives
every code field a storage template and an explicit owner function, with
injectivity and unbounded storage proved. Immutable word headers and fields
remain the word abstraction; G58-G61 now check a selected byte codec, sequential
patch/fetch and native operand geometry. Complete compiler/CPU refinement is separate.

Native spacing is 8 bytes on x86 and 16 on x64, with full-width aligned `A3` /
`48 A3` address operands. Padding precedes called entries or lies in unfetched
storage templates. The linked fixture checks alignment, exact owner opcode
bytes and disjoint intervals. `Native/LittleEndian`, `Native/Encoding`,
`Native/ByteMemory` and `Native/Layout` now prove round trips, exact patches
and universal grid geometry. Their integration with ISA execution remains open.

## Explicit tag guards and control

Check the offset before calculating the dynamic pointer. An encoded offset
lies below the heap base; an encoded address lies at or above it. The offset
guard swaps the base guard's continuation/terminal targets. With a valid offset,
compute base plus offset and check the result against the heap base.
`Virtual.mov_address_two_tests` proves these two tests exactly classify source
address faults for every tagged word. This backend therefore does not require
a separate global reached-offset typing hypothesis. The older typed-base lemma
remains available for an optimized alternative.

A shared guard first captures its caller's return word using a unique inline
DEFADDR operand and stores that value in a resume code word. Further reader CALLs
can then overwrite the common return field safely. The guard compares into
memory, records borrow with memory SBB, selects a target using memory XOR/AND,
resets SP and CALLs the selected target. Its native callee takes 86 instructions,
or 89 including its caller. `ConcreteGuards` and `ConcreteGuardCalls` now prove
those counts through actual fetch, per-instruction code writes, source/metadata
frames, exact return-or-terminal selection and the five-field boundary frame.
Only caller snippet placement remains a premise of the invocation contract.

The generated successful source blocks take 11 instructions for a Boolean
immediate, 233 for an indexed load and 239 for an indexed store. Guard failure
transfers to the terminal observation before any invalid indirect exchange.
These counts now have full fetched compiler proofs in `ConcreteInstructionTails`,
`ConcreteStores` and `ConcreteCompiler`, including fault reflection and arbitrary
source-register aliasing. `ConcretePrograms` composes complete source programs.
Resetting SP before every CALL avoids a growing ordinary control stack. Every
computational CALL, including loop/terminal transfer, writes its return into code.

The backedge CALL reads a code-backed loop target. Native terminal stubs restore
the host stack and report completion outside the pure computational boundary.
`ConcreteLoops` checks the actual backedge, and `ConcreteSimulation` proves
equivalence with the intended terminal and divergence outcomes. `ConcreteTerminalTape`
proves that every reached terminal retains the halted TM's entire tape and head.

## Native implementation and remaining refinement

[generate_pure.py](../validation/generate_pure.py) emits both architectures from
the Lean-exported kernel. [pure.json](../validation/pure.json) records 109 cases,
535 observed passes and 107 genuine closed loops per architecture, including
the original addition output, both tape directions, empty/missing transitions,
invalid tags, aliasing and bounded nonhalting prefixes. Complete source register/
heap states are compared; independent TM examples check the output and head.

The revision-093 Intel SDM is pinned and reviewed in
[ARCHITECTURE_NOTES.md](ARCHITECTURE_NOTES.md). Native realization requires
representable finite traces, allocated initialized storage, correct page and
CET configuration, disjoint fields, valid displacements, canonical x64 pointers,
no unintended address wrap and an adequate self-modifying fetch discipline.
CALL is not claimed serializing. A single finite x86/x64 machine is not an
unbounded-memory machine.

## Remaining completion sequence

1. **Checked at word level:** constructed unbounded shared-routine image,
   unique storage owners, fixed headers and complete metadata/finite-input
   initialization. Kernel and guard snippet placement are proved.
2. **Checked at word level:** explicit offset/base guards, guarded address
   formation, successful/failing source instructions and complete programs.
3. **Checked at word level:** positive loop progress, TM halting/divergence
   equivalence, complete finite-trace tape observation and terminal output recovery.
4. **Checked at word level:** reachable per-instruction code writes, actual
   changes arbitrarily late in every nonhalting initialized TM execution, and
   an explicit walker changing owned fields beyond every finite address bound.
5. **Finite execution/encoding checked:** `FiniteExecution` matches every word
   prefix with a list journal, and `FrozenTM` replaces transition callbacks with
   finite table data. `ConcreteFiniteExecution` closes the default/header lookup
   inputs and preserves outcomes; `FiniteSerialization` gives an injective,
   reversible natural-list encoding. The fixed algorithms and scalar primitives
   now have TM computability and positive-step converse certificates.
   G37-G39 check both finite machine adapters and
   connect actual Mathlib TM0 evaluation and output to pure SMC.
   G40-G46 certify journal operations, signed arithmetic and bitwise operations,
   state packing/parsing, all instruction effects, operand resolution and the
   actual fixed-image header lookup as primitive recursive. G47-G49 additionally
   certify finite machine descriptors, the actual initial-word generator and the
   complete bounded loop, with exact semantic agreement including faults.
   G50-G53 check the unbounded partial-recursive search, actual TM2/TM1/TM0
   composition, finite support, positive compiler progress and complete journal
   recovery. G54-G56 additionally check literal finite-label restriction,
   blank/start-preserving numbering and composition with the source/SMC adapters.
   T13 is complete in the word model. G57 instantiates the unchanged repository
   addition table/input: 132 steps, genuine halt, head 10 and `1101_0000_`,
   with complete terminal pure SMC tape/head recovery.
   The partial-recursive-code/TM2 certificate route and pinned dependency
   are specified in [TM_LIBRARY_PLAN.md](TM_LIBRARY_PLAN.md).
6. G58-G61 check the selected byte codec, byte-memory patch/current fetch and
   affine native layout. G62 checks full-word SBB masks, tag guards and indexed
   addressing under capacity bounds. G63 checks a non-faulting selected ISA
   projection with current-byte packet execution, decoded-trace CF preservation
   and aliased CALL pushes. G64 derives packet lengths from the live opcode
   header and proves automatic-fetch CF/SBB bridges. G65 checks each full word
   write and the complete four-instruction byte reader contract, with live
   MOFFS validity for exact self-alias or complete-packet disjointness. G66 checks
   full SP-reset restoration, fixed-slot CALLs and reusable StackTop; G67 composes
   the complete shared reader callee and caller return/memory/CF contract.
   G68 constructs the register/heap byte storage grid, proves exact initial
   words/opcodes and preserves all owner opcodes along owned-write traces.
   Current MOFFS fetch and no-wrap natural/encoded-address loads are checked.
   G69-G70 construct finite control/metadata packets and the combined control/grid
   image, with computed separation, exact initialization and owned-write byte
   preservation. G71 constructs the four-instruction reader and derives its
   addresses, all automatic fetches and owned destinations; exact initial grid
   loads and the complete sequential boundary state are checked. G72 checks
   signed rel32 extension and computed absolute/RIP/relative-CALL targets,
   including backward transfers and SBB's complete instruction size.
   G73 checks finite fragment views, exact encoded metadata and distinct
   owned-field separation, extending readers to metadata and self-aliases.
   G74 constructs reset/CALL packets and derives their fetches and transfers.
   G75 constructs the seven-instruction callee and derives every fetch/address
   premise, actual ownership, complete boundary state, preserved image and
   reusable StackTop. Finite code operands initialize StackTop and the pointer.
   G76 composes the ten-instruction placed read caller round trip, including
   return-field aliasing and exact memory restoration. G77 constructs the shared
   store-entry callee; G78 composes its seven-instruction caller round trip with
   exact destination/return writes, AX/CF preservation and reusable StackTop.
   G79-G80 compute finite placement with explicit padding, exact initialization,
   gap framing and owned-write preservation. All global fragment/read/call/callee
   and read/store invocation contracts now use the padded image. G81 derives
   the generator's reader/scalar ALIGN formulas and bounded field alignment.
   G82 constructs those fixed scalar MOV/ADD/SUB/XOR/AND/SBB packets with derived
   current-byte fetch/address/ownership, exact modular/CF effects and frames.
   G83 composes the 13-instruction SUB/read-zero/MOV/SBB borrow-mask stage, derives
   every intermediate readiness/zero value, and checks exact mask/CF and reusable
   boundary/frame state. G84 checks the 26-instruction capture/setup prefix,
   with the original caller return word captured/saved before nested CALLs and
   exact original candidate/Scratch/boundary, CF and reusable image/stack/frame
   contracts. Its executed readiness is derived from initial-memory setup.
   Fixed MOV now matches MASM's actual 5/7-byte x86/x64 forms; scalar and
   borrow-mask contracts are rechecked. G85 checks complete eleven-instruction
   reader/scalar updates. G86 checks the complete 47-instruction selector/return,
   exact mask/target, derived readiness, only final Selected/Slot writes, CF/AX/SP
   and reusable image/stack/field frames. G87 now composes the complete
   86-instruction guard, deriving actual borrow/selector readiness through
   setup/borrow writes and physical metadata frames. G88 adds the actual caller
   and checks the 89-instruction round trip, derived post-call readiness,
   original-value borrow and computed outer-return/terminal selection for both
   Base/Offset orientations. CF/AX/SP, exact memory, current-byte fetch, all owned
   writes and reusable image/StackTop/frames are checked.
   G89 connects literal Dolan words to native 0/stride offsets and heap pointers,
   with no-wrap injection, actual guard tag classification and correct indexed
   addresses, including rejection of wrong offset-valued bases after addition.
   G90 constructs the complete bounded source-data representation and initializer
   in the native register/heap code grid. G91 connects the actual eleven-
   instruction immediate block to source MOV execution and the full represented
   register/heap result, with current-byte trace, owned writes and reusable state.
   G92 derives actual post-read guard setup across Candidate/Slot writes and
   checks the complete 100-instruction offset-read/guard prefix, exact original
   source tag and computed continuation/failure word, full represented source
   frames and reusable current-byte/owned native execution state.
   G93 checks the 33-instruction active-operand construction with source-data
   and owned-metadata frames. G94 derives both later stage setups from the
   executed offset prefix and composes the complete 100/222-instruction
   address paths, exact source address decision and selected shared operand.
   G95-G96 check the complete 233/239-instruction load/store effects and traps,
   allowing source-register aliasing and deriving actual reader/store setup.
   G97-G99 compose source blocks and the actual backedge, and lower the exact
   64-MOV kernel with checked instruction/PC/grid correspondence.
   N00-N17 construct the inline source/guard packets, complete aligned prefix,
   initialized roles and a self-consistent common image context. Literal
   placement derives initial reader/scalar/read-update readiness, both complete
   guard certificates, the initial loop invariant and actual backedge setup.
   N18-N22 derive every compiled source block's initial Ready, immutable
   metadata frames and every field of ProgramImage.Setup; exact entry/end PCs
   and the complete bounded/closed byte pass are checked. N23-N27 construct
   finite loaded execution and output/ownership refinement for both passes.
   Next bound the computed access extent by a prescribed mapped/canonical
   allocation and connect hardware execution under explicit fetch conditions.
   Apply relocation/capacity/canonical-address bounds to the emitted image and
   close hardware fetch discipline; connect the complete native generator to
   those verified contracts. Extend tests only for new changes or
   uncovered contracts; the current full native suite passes.
7. Audit all original completion gates, source adaptations, appendix and
   ancillary obligations. The complete goal remains active and incomplete.

G95-G96 check the complete native source load and store blocks. Both derive later reader/store setup from the executed guarded address stage and original static placement. The computed pointer is the single active operand shared by load and store. A successful load performs the literal source register update while preserving every other register and heap word; a successful store updates precisely the selected heap word and preserves all registers and other represented heap words. Source register names may alias. Malformed offsets stop after 100 instructions, malformed bases after 222, successful loads after 233 and stores after 239. Exact source outcomes, complete represented-state effects, current-byte traces, code-owned writes, owned-word frames and reusable image/StackTop/SP/CF are checked under explicit cell/no-wrap bounds. N18-N22 close whole emitted role/compiler instantiation under explicit capacity/compactness and source-path bounds. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

G97-G99 check native program composition, the actual backedge, and lowering of the exact exported 64-MOV kernel. Block readiness is derived from one initial metadata snapshot, physical field separation, the intact image and the actual selected heap pointer; no later trace or Ready is assumed. Finite schedules stop at the literal source trap and preserve all represented source data and code ownership. Successful schedules reach the computed end PC with a reusable invariant; the reset/indirect CALL composes into a closed pass. The kernel layout pass preserves all 64 instruction operands, a common source grid and contiguous encoded PCs. Its address-immediate rejection is explicit: the fixed kernel uses only offset immediates. N18-N22 now derive the complete static placement/metadata certificate from the padded emitter image and prove its full bounded/closed byte pass. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N00-N01 construct the literal inline packet sequences for all source blocks and both shared guards. The exact exported kernel has 1,678 source-body packets, and each guard has 37 inline packets. Physical source/guard positions, finer reader-caller/scalar-entry placement and whole-body embeddings in the padded image are derived from the packet builders. For compiled source schedules, explicit static end-position bounds discharge the conversion from encoded continuations to natural byte positions. N02-N08 now construct that aligned prefix, resolve its addresses and initialize all roles in the complete emitted byte image. N09-N17 derive context consistency, initial reader/scalar readiness, both complete guard certificates, the initial loop invariant and backedge setup. N18-N22 derive every compiled source block's initial Ready, immutable-role frames and the full source-schedule certificate. N23-N27 now construct finite loaded-prefix equivalence. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N02-N08 add 50 checked declarations for aligned templates and finite pools, literal role initialization, native byte lengths, affine metadata separation, the two-pass address allocator and complete byte-image initialization. The exact kernel occupies 9,382 bytes in x86 and 10,816 in x64; guards occupy 206 and 244 bytes. The constructed image contains all 23 shared readers, both guards, source body, backedge and 13 metadata owners; the host observation gap remains unfetched backing bytes. All reader and metadata operands have computed initial values, ownership and alignment, and represented source words initialize correctly in the protected data grid. N09-N17 prove that the source reference context equals this constructed whole and derive the guard and backedge certificates. N18-N22 derive every source block's initial Ready and the full source-schedule Setup. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. `ExportLayout.lean` supplies the allocator's coordinates for an independent finite MASM comparison; that comparison is evidence, not a proof of the Python generator or hardware semantics.


N09-N17 add 76 checked declarations. The fixed compilation now constructs a self-consistent complete byte image; all 23 reader and 13 metadata fit conditions follow from one finite source-grid capacity bound. Metadata fields, reader operands and both guard captures have injective physical and encoded addresses. Literal placed bytes and initialized operands derive reader/scalar/read-update readiness, both complete guard orientations, the initial represented/intact/frame/selected invariant and backedge Setup. Fixed control/register relocations use the explicit compactness condition `heapBase - origin < 2^31`; heap MOFFS operands use full-width capacity bounds. N18-N22 derive its frames across every compiled source block and each block's initial Ready, closing every field of `ProgramImage.Setup`. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. Overall completion remains incomplete.


N18-N22 add 38 checked declarations and close the whole emitted source-schedule certificate. Each block has an actual lowerer witness; its static observations belong to the constructed immutable role set, and that set is disjoint from its complete final-write destinations. All immediate/load/store initial Ready predicates follow from literal placed packets and initialized bytes, with source-register aliasing permitted. `ProgramCertificate.source_setup` supplies every field of `ProgramImage.Setup`; exact entry/end/Linked PCs and a full current-byte/code-owned bounded kernel pass are proved. `closed_pass_correct` composes an accepted pass with the actual backedge and restores the full invariant at kernel entry. Capacity, `heapBase - origin < 2^31`, positive cells and the path's source-address bounds remain explicit. N23-N27 construct finite loaded execution. N43-N55 close the allocation extent bounds. Physical mapping/canonical conditions, coherent hardware fetch, remaining source/appendix proofs and registry packaging remain open. Overall completion remains incomplete.

N23-N27 add 44 checked declarations for finite loaded-memory refinement. A finite byte image stores exactly the loaded interval; its partial evaluator automatically fetches current bytes and accepts only contained header/packet, data-read and full-word-write windows. Loaded-byte agreement preserves all selected scalar effects, write addresses/values, traces and ownership while framing exterior bytes. A computed containing interval supplies safety for every finite fetched prefix without assuming a safe execution. The whole emitted kernel and accepted body plus actual CALL backedge now have constructed finite loaded executions with literal source outcomes and every represented register/heap word preserved. The extent includes the complete represented finite grid. N43-N55 close containment in the prescribed allocation. Physical mapping/canonical conditions, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N28-N35 add 38 checked declarations for bounds in one allocation fixed by the emitted layout and requested finite source grid. Every placed control entry has a contained fifteen-byte fetch window; complete metadata, register, selected heap and all 23 initial reader-pointer words are contained, and the allocation fits the finite machine address space. Initial pointer/StackTop values and actual executed-state frames derive bounds for the repaired reader, reset/CALL, seven-instruction callee, ten-instruction caller round trip, each scalar operation and eleven-instruction read/update. Literal initialized placed callers and read/update fragments therefore have finite loaded executions in this prescribed allocation. N36-N42 compose the guards; N43-N55 complete the dynamic source and whole-kernel allocation certificate. Canonical-address validity, permissions/segmentation/CET, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N36-N42 add 22 checked declarations composing the fixed-allocation bounds through all guard stages. Static packet placement derives reader/callee/scalar/CALL fetch windows from one control interval. Proved pointer frames derive every data-read and complete word-write bound through the 26-instruction capture/setup, 13-instruction borrow-mask and 47-instruction selector/return stages. Both 86-instruction guard orientations and the actual 89-instruction outer invocation have finite loaded executions in the preselected allocation, derived from the initialized emitter image, capacity/compactness and typed metadata; no future safe trace or intermediate Ready is supplied. N35 additionally proves containment of the whole static control interval, bringing its declaration count to 19. N43-N55 close the remaining dynamic source and whole-kernel allocation bounds. Physical canonical/permission/segment/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.

N43-N55 add 31 checked declarations closing dynamic source and whole-kernel bounds in the allocation fixed before execution. Pointer construction reads contained register and operand words without dereferencing an unvalidated value. Successful load/store operands are proved equal to the selected contained heap word from source representation and finite-cell bounds; rejected tag paths execute their contained guards. All actual compiled blocks obtain static certificates from their literal lowerer witnesses. Schedule induction derives current Ready from the preserved invariant at every boundary, then composes the complete emitted body and actual reset/indirect CALL backedge. `ProgramAllocation.kernel_loaded` and `closed_loaded` construct their finite loaded executions with exact source outcomes, every represented register/heap word, code-owned writes and the closed entry PC. No future safe trace, intermediate Ready or trace-dependent allocation extent is supplied. Address-space capacity, compact relocations, positive cells and source-path cell bounds remain explicit. Physical mapping, canonical/segment/permission/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.


N56-N58 add 22 checked declarations for configured canonical-address intervals
and effective read/write/execute permissions. Static fixed-allocation endpoints
and RWX conditions derive every current-byte fetch, selected read and complete
write check through the actual kernel and CALL backedge. The checked partial
evaluator retains exact source outcomes, all finite represented data, code-owned
writes and the closed entry PC; invalid PCs or absent execute permission are
explicit rejections. Physical ISA/configuration/current-fetch refinement and
literal source/appendix/registry obligations remain open. See
[ARCHITECTURE_NOTES.md](ARCHITECTURE_NOTES.md#checked-allocation-and-effective-permissions-n56-n58).


N59-N60 add five checked declarations for actual CALL-target validity. Interior
targets are PCs of the next contained instruction; an accepted closed pass ends
at its contained initial entry. `ProgramControl.closed_checked` therefore retains
full output/ownership and memory-window checks while deriving every CALL target,
including the final backedge. The rejected source/host endpoint remains N61;
physical ISA/configuration/current-fetch refinement remains separate.


N61-N64 add twenty checked declarations closing rejected source/host endpoint
validity and combining all modeled checks in one finite evaluator. The original
frozen terminal value determines the actual final PC; `terminalOffset < hostSpan`
and fixed allocation/capacity derive containment, no-wrap and canonical validity.
`SourceChecked.kernel` and `closed` construct live-byte checked executions with
all fetch/read/write/permission/CALL-target checks, exact source outcomes, full
finite output, code ownership and endpoint PC. The MASM audit checks the actual
host-span condition. Physical ISA/configuration/current-fetch refinement and
literal source/appendix/registry obligations remain open.


N65-N67 add eight checked declarations for continuous repeated native passes.
A source-driven bounded iteration threads each actual resulting byte state into
the next body/backedge, stops at the first rejection and keeps one original
snapshot invariant. `SourceIteration.checked` constructs one finite checked trace
with exact source outcomes, every finite source word, code-owned writes, all
modeled checks and entry/terminal PC. Accepted runs contribute at least three
events per pass. No future native trace or repeated initializer is supplied.
Physical ISA/configuration/current-fetch refinement and literal source/appendix/
registry obligations remain open.

Y02 now checks the split-word value contract in
[X64/HalfWords.lean](SmcTuring/X64/HalfWords.lean): corresponding-half Boolean
operations and MOV lift exactly, while OP64 immediates repeat a 32-bit mask.
The full ADD/SUB equations include carry/borrow; the independent forms have
explicit no-carry/no-borrow premises and checked counterexamples. M04 in
[ERRATA.md](ERRATA.md) records the interpretation. Literal half-field placement,
exchange/alias/flag and supplementary purity obligations remain open; the
adapted full-width native backend is unchanged.

E06-E08 check the literal Listing 10 predicate and displacement-patching
prefix in a 32-bit field-word model. All six signed/unsigned relations, signed
boundaries, operand/low-accumulator restoration, complete word/CF frames, actual
patch selection, modular target, 10-17 events and conditional code-write purity
are checked. M05 records separate storage and independent target input; the
MASM audit confirms bracketed NEAR-label CALL remains E8 rel32. E15-E24 close reference byte owners,
live fetch and continuation IP/layout; general host spacing/physical ISA remain E02/E05; E09 now checks the
word/register stack/CALL and JUMPTARGET composition. See
[APPENDIX_BRANCHING.md](APPENDIX_BRANCHING.md).

E09 additionally checks 23 declarations for the printed x86 single-XCHG/CALL
and JUMPTARGET word/register effects, including the real return-slot/MOV-address
alias and composition with all signed/unsigned branch predicates. Exact boundary
words and ESP are restored; nonwrapping continuation ADD gives CF=false.
E15-E24 close reference byte owners, current fetch, tail/continuation and both
end PCs. General host spacing and physical ISA/fetch remain open; E10 now supplies whole native branch tests and E11 supplies packet patch/fetch proofs. See `APPENDIX_BRANCHING.md` for the precise scope and assumptions.

E10 supplies 74,400 normalized whole x86 branch cases across all 12 relations,
with exact GPR/ESP/CF/owner-word and other-code-byte checks. E11 adds 24 kernel
packet codec/current-patch proofs; 13 Lean encoding exports are compared directly
with 338 MASM headers, 84 actual fields and 338 symbol-target relocations.
E12-E14 now establish selected byte effects and finite field-word prefix
refinement. E15-E24 close reference own operands, headers, continuous live fetch and
byte tail/continuation composition. General host spacing and physical ISA/fetch
remain open. See `APPENDIX_BYTE_CODE.md` for the precise contract.

E12-E14 add 68 selected-byte/finite-field branch declarations; all selected forms
have PC/EAX/ESP/CF/write effects and the prefix has all-relation displacement,
register/word/CF and exact exterior-byte restoration results. The finite field
view requires complete 32-bit capacity and four-byte separation. Actual emitter
own-immediate identities, intact headers/constants and continuous live fetch
from one initialized reference image are now derived in E15-E24, including the
byte tail/alias and both continuation end PCs. General host spacing and physical
ISA/fetch remain open.
See [APPENDIX_BYTE_CODE.md](APPENDIX_BYTE_CODE.md).

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

The requested minimal M01-M06 errata is now standalone LaTeX plus an exact
source-checked excerpt diff, with short positive proofs. Y04 then adds 28
checked selected split-word exchange/copy/NOT frame results and native x64
printed patterns/x86 paired primitives, each 17,290 cases. Source halves, low
accumulator, CF, unrelated words and all non-target code bytes have explicit
contracts. Native half-field placement, arbitrary USEOP/full CPU and remaining
supplementary algorithms remain ledger work. See `X64_SPLIT_FRAME.md`.

E31-E33 now check Listing 11 multiplication algebra, literal mutable-word
blocks and the complete actual-displacement data/control loop. For all
32-bit inputs it terminates, produces the modular product and restores
inputs/AX/CF/displacement with whole-data-trace purity and exterior-word frame.
E34-E36 now close literal CALL/SP continuation and actual-PC execution. The
immediate next bridge is complete current-byte loop fetch/layout; supplementary constant multiplication and
division follow. M07's four substitutions are already in the compact errata.

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


E53-E55 close Listing 6 constant multiplication at the arithmetic and complete
compiled-word levels, with 41 checked declarations. Preserve the printed
emitter: M08 changes Leading to Trailing and the two later shift counts to
NLZ+1; zero/unsigned-bit-pattern/logical compile-time consumption and omitted
initial zero shift are local conventions. The native reconstruction passes
54,366 cases and compares 11,350 complete pure packets/79,534 original-image
bytes against the checked Lean emitter. Generic current-byte execution and
remaining auxiliary data operations retain E01/E05. Next connect its variable
SHL/count forms and patched final ADD to the existing byte-image machinery;
division, remaining literal/half-field placement, other branch geometry and
physical/registry obligations remain in scope. The compact M01-M08 errata is
still two pages, checked against 19 original excerpts and 48 positive proofs.


E56-E62 close that generic current-byte bridge under static image facts, adding
99 checked codec/effect/refinement/image/packing/current-fetch/composition
results. Derive the complete variable emitter's static placement and own ADD
immediate next: prove address-independent span, the unique final ADD location,
and its scratch=PC+6 identity, then construct separated original data/scratch
owners and apply `ConstantSimulation.original_image_correct`. The native
comparator already matches all actual Lean-coded packets and owner offsets.
No new source correction is required. Auxiliary data operations, division,
remaining literal/half-field placement, other branch geometry and physical/
registry obligations remain in the full scope.


E63-E66 close the whole variable constant-emitter geometry and original-image
live-byte contract with 44 further proofs (184 constant-emitter proofs total).
All static placement/own ADD operand/ownership/capacity facts are now derived.
Only original image, entry and complete extent are required for the all-input
product, complete live trace, EAX/ESP/CF/endpoint, owned writes, reusable image
and original exterior bytes. Repeated execution permits arbitrary current
data/scratch under the preserved invariant. The comparator checks actual
Lean-computed whole-image coordinates, complete packets and owner fields for
all 663 constants, retaining 54,366 cases/11,350 pure packets/79,534 bytes.
Auxiliary Listing 6 DEFZERO/conversions are the next E01 work; division,
remaining literal/half locations, other branch geometry and physical/registry
gates remain in the full scope. No new paper erratum is required.


E67 closes corrected DEFZERO with 18 positive current-byte proofs and 9,312
native executions/582 words on each architecture. `run_zero.py` compares the
actual complete MASM/Lean packet and real x86 absolute/x64 RIP owner address,
all GPRs/SP/CF/exterior bytes and repeated use. M09 retains the one XOR and
uses explicit DWORD typing plus existing CNSTFRC32. The compact errata still
has two pages, with 20 exact excerpts and 53 positive audited references.
The full audit has 2,743 declarations/302 unique ledger IDs. Next E01/P04 work
is Listing 6's code/data conversion and template copying/relocation; division
and remaining literal/half-field/branch/physical/registry gates retain scope.
After refreshing run_lean.py, also run `python validation/run_zero.py` before
the final aggregate evidence audit.

E68-E77 close full-width USEWORD conversion and the positive TRANSFERDATA
byte/plan/cursor/field/codec contracts; M10 is the six local cursor-operand
substitutions with the example's existing cursor arguments. E78-E82 add 54
instruction/body/template results: actual SI/DI/DF byte execution, universal
word-index refinement, the complete initialized MOVS body's actual-PC/live-fetch
trace, exact copied-packet decoding and internal RIP/external absolute target
laws. The full audit covers 2,901 declarations/317 ledger IDs, with all complete
native macro packets also live-decoded by the actual Lean classifier/fetch.
No additional paper correction is required; M01-M10 remain 28 exact edits and
59 positive references in the checked two-page errata.

Continue P04 by constructing the actual initializer/index-exchange/SUB forms
and their live packet invariant, deriving the temporary cursor values and all
address hits from initial placement, and composing those stages with
`StringMoveTrace.correct` and the existing exact restored-field proof. Retain
the actual x64 DEFDATA accumulator effect. Then construct complete copied-template
absolute/MOFFS address initializers and apply `StringTemplate`'s retained-fetch
and internal RIP laws. Division/remainder, other branch placement orders,
literal Listing 8/9 and x64 half-field locations, physical ISA/fetch and registry
packaging remain the full-goal gates.

E83-E90 add 50 original-window, actual initializer/prefix/restoration and exact
legal-program encoding results. The full audit covers 2,951 declarations and
325 unique ledger IDs. The native comparator checks the complete actual form-list
encoding and original prefix bytes for every macro, supplementing the live
classifier/fetch checks. Both DEFDATA variants have actual traces, with full
memory/SI/DI/SP/CF/DF retention and the actual x64 AX result. The complete setup
prefix and restoration pairs have derived traces/state effects. No new erratum
is needed; the compact M01-M10 document and exact minimal diff remain unchanged.

Continue P04 with single-original-image continuous macro trace/final-state
composition and derived backward tail RIP placement bounds, then whole-template
absolute/MOFFS patching. All remaining division, branch, literal/half-field,
physical and registry gates remain in the full goal. Refresh the full Lean/native
suites and final encoding/errata/evidence audits after each proof refresh.

E91-E94 add 46 checked results for the complete corrected TRANSFERDATA macro,
bringing the audit to 2,997 declarations and 329 unique ledger IDs.
`StringMacroTrace.correct`/`run_correct` derive continuous actual-byte/PC
execution and exact full final state from one original image and static
complete-word/copy/code resources. Every stage fetch/readiness and saved index
load is derived, as are all four backward tail rel32 bounds. Both SI/DI and
cursor pointers return to their original values, source/code/exterior bytes
are retained, and `reusable`/`reentry_trace` derive the next run after PC reset.
Native x86/x64 each retain 6,144 passing executions/48 sizes, now also checking
those exact static resource/range bounds. M01-M10 and the compact errata remain
unchanged. Next P04 work is whole-template absolute/MOFFS patching and copied
relocation; remaining algorithm, placement, physical ISA/fetch and registry
gates retain their full scope.

E95-E97 add 41 checked complete-template compiler/copy results (3,038 audited
declarations / 332 unique ledger IDs). `TemplateRelocation` binds all internal/
external MOFFS words, all ten memory operations' absolute/RIP displacements and
near CALL displacements for the independently chosen destination. Packet sizes
are invariant, including SBB's trailing immediate. Natural target capacity and
signed reach are explicit. Internal RIP/CALL fields retain their displacement
when referents move; absolute internal pointers are initialized for destination
addresses. The paper explicitly permits compilation or runtime initialization.

`TemplateCopy.compiledImage` installs both original byte images in one memory.
`original_image_correct` derives initial readiness, the complete copying trace,
every destination byte and every actual packet fetch from compilation/static
resources. No original/future image, load, address hit, Ready, fetch or trace is
supplied. This closes P04 through the paper's compile-time route. The checked
runtime USEWORD field conversion remains available; arbitrary copied programs
retain their own algorithm execution contracts.

Independent MASM fixtures x86/x64 each pass 768 copying executions across four
forward/backward layouts. All 15 packets/template cover both MOFFS reference
kinds, all ten memory operations, internal/external near CALLs and indirect
exchange. Every copied byte, PC/length/live fetch and resolved address matches
Lean: 332/412 template bytes and 60 destination headers per architecture.
Source/destination/cursor/GPR/SP/CF/code/reuse frames pass. M01-M10 and the compact
errata remain unchanged. Refresh with `python validation/run_template.py` after
the Lean audit and before the aggregate evidence audit. Division/remainder,
other branch geometries, literal Listing 8/9/finalization/half-field placements,
physical ISA/fetch and registry gates retain their full scope.

`TemplateCopy.original_addresses_correct` joins every live destination fetch
with its exact natural address meaning. Static `ReferencesValid` supplies
per-packet signed reach and full target capacity; these are compiled-layout
properties, not future address-hit or execution assumptions.

E98/E99 supply the next division foundations: all unsigned DWORD arithmetic,
same-word trial bounds, and four proved minimal Listing 12 repairs. Continue
with the original signed normalization/result instructions, then the actual
32-pass word/CALL/continuation loop and original-image current-byte/native
construction. Preserve the printed indentation; only M11's four substitutions
and the already recorded M06 counter spelling are code corrections.
