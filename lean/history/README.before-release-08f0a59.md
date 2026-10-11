# Lean formalization of smcTuring


**Current verification policy (2026-10-06):** Lean is pinned to
`leanprover/lean4:v4.35.0-rc3`, commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`.
Run every build/test command serially through `validation/limited_run.py`.
Windows caps aggregate committed allocation at 1.5 GB; a 25 ms monitor also
stops the job at a conservative 1.5 GB resident threshold. Direct Lean uses
`-M768 -j1`. Never retry a capped failure without the guard.
The cursor and complete input-update fragments add 63 and 38 declarations.
The prior 3,734-declaration/sixteen-native-suite snapshot is historical;
the changed worktree's whole-library audit and all native evidence are being refreshed.
The complete rc3 import-artifact map includes core modules and preserves
required private import levels. This resolves the Mathlib adapter's capped
import failure; its unchanged proof has compiled within the cap.
`validation/bounded_build.py` compiles modules serially. The main audit can
reuse a completed build only after `bounded_snapshot.py` checks all source,
configuration, setup, imported-artifact and compiled-artifact hashes.
`validation/refresh_evidence.py` then runs each proof/native/evidence phase
in a separate capped job, sequentially, stopping at the first failure.


This directory holds the plan for formalizing Gregory Morse's 2018 paper,
*Pure Infinitely Self-Modifying Code is Realizable and Turing-complete*
([DOI 10.24425/119359](https://doi.org/10.24425/119359)).

Start with [PROOF_LEDGER.md](PROOF_LEDGER.md). It defines the intended results,
dependencies, assumptions, source-alignment questions, and completion gates.
The remaining implementation is detailed in [SMC_COMPILER_PLAN.md](SMC_COMPILER_PLAN.md),
with an explicit [completion audit](COMPLETION_AUDIT.md).

**Status, 2026-10-06:** the pinned Lean v4.35.0-rc3 project checks the DEFADDR
repair, the fixed 64-MOV TM simulator, its four-register compilation, and the
complete pure SMC simulation in the unbounded word model. The constructed image
fetches mutable operands from current memory. Its guarded compiler, actual
code-backed backedge and finite-input initializer have checked execution proofs.
TM halting and divergence are equivalent to the intended SMC outcomes, and
every reached computational instruction writes an owned code field.
Every nonhalting initialized TM causes actual code changes at arbitrarily late
instruction times. A separate one-state walker changes fields beyond every
finite address bound. The entire tape and head are recovered at finite TM
boundaries and at the intended terminal. The fresh complete Linux axiom audit covers 3,835 declarations in 366 modules; Windows bounded and native validation remain pending.
The finite-data evaluator matches every word-model prefix, including faults.
Transition tables are frozen into lists and reached states have reversible
natural-list encodings. All journal, signed arithmetic/bitwise, instruction,
header and initial-word algorithms, and the bounded loop, are certified
primitive recursive. Unbounded terminal search is partial recursive and
compiled through actual library TM2/TM1/TM0 evaluation. G54-G56 restrict its
control support to literal finite labels, number symbols/labels while retaining
the blank and start, and compose the existing source/SMC adapters. This closes
T13, including positive progress and complete terminal-journal recovery.
The repository addition example is also kernel checked: 132 transitions,
undefined state 2, head 10 and output `1101_0000_`, with a terminal pure SMC
run retaining the complete tape and head.
The imported Mathlib TM0-to-SMC compiler preserves actual partial evaluation,
including halting, nonhalting code changes and the complete relative tape output.
The reverse adapter covers arbitrary source machines with three finite labels
per source state and two TM0 steps per transition, preserving halting and output.
G58-G61 additionally check the selected x86/x64 instruction codec, byte stores,
MOFFS patch/current fetch and affine operand ownership/layout. G62 checks
finite-word borrow/mask selection and indexed pointers under capacity bounds.
G63 checks a selected non-faulting ISA projection, current-byte packet execution,
CF preservation through decoded reader/call traces and aliased CALL pushes.
G64 derives the selected packet length from at most three current opcode bytes;
automatic fetch uses live operand bytes and preserves CF through reader/CALL
bridges. G65 proves complete word writes, exact byte-memory restoration and
all four repaired reader effects, including owned destinations and live-packet
safety for exact self-alias or complete-packet separation. G66 proves complete
byte restoration through SP reset, fixed-slot CALL effects and reusable StackTop;
G67 composes the complete seven-instruction shared reader and caller/callee
return contract, including owned writes and preservation outside the return field.
G68 constructs a concrete register/heap byte storage grid, checks every initial
word and owner opcode, and preserves all owner opcodes through actual owned-write
traces. MOFFS fetch uses the current operand, and an explicit no-wrap bound
connects natural operand loads to encoded CPU addresses. G69-G70 construct finite
control/metadata packets, compute disjoint placement, initialize the combined
control/grid byte image and preserve both regions through owned-write traces.
G71 constructs the repaired reader, derives its addresses and all four fetches,
and proves the exact initialized-grid result. G72 checks computed signed rel32,
RIP/absolute addresses and relative CALL targets in both widths, including
backward transfers and SBB's complete length.
G73 proves finite fragment embeddings, exact encoded metadata loads and byte
separation of distinct owned fields. Reader pointers can name scalar metadata,
other readers, grid fields or their own label, with derived fetch safety. G74
constructs reset/CALL packets and derives their fetches and computed transfers.
G75 constructs the complete seven-instruction callee, derives every fetch and
resolved-address premise, checks its exact return/memory/accumulator/SP/CF state,
and preserves the full image. Encoded operand initializers supply StackTop and
the pointer; distinct owned top/slot fields make StackTop reusable.
G76 proves the full ten-instruction placed read invocation, including the
return-field alias and complete memory restoration except for the final return
word. G77 constructs the four-instruction store callee at the same mutable
MOFFS instruction used by the reader. G78 proves the seven-instruction placed
store invocation, its computed return position and exact destination/return
writes. Byte-store commutation removes the caller's intermediate push from the
final memory equation. Both invocations preserve CF, reusable StackTop and the
whole image; the store also preserves AX. Ownership derives byte separation,
with the store destination distinct from StackTop and the return field.
G79 computes finite packet placement with explicit padding, derives separation
and exact byte initialization, and embeds contiguous bodies in the padded
sequence. G80 preserves the complete padded control/grid image through owned
writes; uncovered bytes before the grid initialize to 90h. The global fragment,
reader, reset/CALL, callee and read/store invocation contracts now use this
context. G81 checks the generator's ALIGN formulas: 2/5 extra bytes for reader
labels and 3/6 for scalar owners on x86/x64, with no-wrap lifting to aligned
encoded field addresses. Whole emitted role-layout instantiation remains open.
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
contribute 30 audited declarations. Complete pointer construction/Base guard,
233/239-instruction source load/store effects and traps, whole role/compiler
instantiation and hardware region/fetch refinement remain open.
Whole generated-kernel role layout and
guard/source-block/compiler realization, applied capacity/canonical/relocation
bounds and hardware fetch remain open.
The full objective remains incomplete:
CPU refinement and the remaining
source, appendix and ancillary obligations are still open. Submission is pending.
See [ERRATA.md](ERRATA.md) and [validation evidence](../validation/lean.json).

The complete finite native kernel passes on x86 and x64: 109 cases, 535 observed
kernel passes and 107 computations using the genuine backedge per architecture.
It reproduces the original addition output `1101_0000_`. The kernel is exported
from Lean and lowered by [generate_pure.py](../validation/generate_pure.py);
its logical registers occupy instruction operands, with accumulator/SP hardware
scratch. [pure.json](../validation/pure.json) records linked-layout checks,
tests, source hashes and disassembly hashes. Native tests do not close the
byte/CPU refinement or remaining full-scope proof obligations. See
[ARCHITECTURE_NOTES.md](ARCHITECTURE_NOTES.md) for the pinned assumptions.

The core deliverable now proves universal computation in the stated unbounded
code model, with an instruction-level code-write invariant. Focused
x86 and x86-64 refinement theorems follow, under explicit resource and execution
assumptions. A complete formalization of the paper's mathematical algorithms
also includes the separately tracked appendix obligations.

The existing C++/MASM programs supply comparison algorithms and a worked input.
They do not yet supply the paper's pure SMC implementation: their memory writes
target allocated data and their control flow includes ordinary branches.

The library currently contains `Memory`, `Defaddr`, `Turing`, and Dolan's
`Primitives`, `Tape`, `Machine`, `Programs`, `TapePrograms`, `TapeEncoding`,
`Initialization`, `Advance`, `TapeStep`, `Frames`, `Guard`, `Transitions`,
`TableLayout`, `TablePrograms`, `WriteValue`, `Matcher`, `AdvanceEffect`,
`KernelState`, `Kernel`, `Scan`, `Progress`, `Simulation`, `FourRegisters`,
`FourWalk`, `FourOperations`, `FourCompile`, and `FourSimulation` modules. The
Turing model uses finite states and symbols, a two-sided tape, and finite input.
`Simulation.fixed_mov_simulation` gives one machine-independent 64-MOV body
with equivalent TM halting and divergence. Each successful TM step needs a
positive, alphabet-bounded number of body passes; rejected entries preserve
the configuration. `simulate_run` also preserves the complete output tape.
Initialization queries the supplied finite table and a blank/link generator,
without information about future execution. `FourCompile` proves successful
instruction effects, fault preservation, and whole-program compilation.
`FourSimulation.four_register_mov_simulation` composes this with the simulator
to obtain one fixed four-register body of 2,252 MOVs with equivalent TM halting/divergence.
The unbounded model, explicit backedge, invalid-zero halting, and source
normalizations are part of the statement's scope.
The `SMC/` modules contain unbounded integer word operations, instruction effects,
current-memory fetch, read/copy/mask primitives, numeric source representation,
metadata frames, successful MOV lowering, word-image execution, and the guard.
`Lowering.compile_run` proves effect blocks for successful source runs;
`Lowering.compile_image_run` additionally requires independently proved image
placement and storage-template coverage. These are intermediate contracts, not
a constructed byte-level interpreter. `boundary_change_has_instruction_change`
separates actual code changes from writes; `ImageChanges` proves this for fetched
execution. `VirtualInstructions` proves immediate/load 11-instruction and store
7-instruction effect tails under placement and valid-pointer hypotheses. The
`Concrete*` modules construct the word image and initializer, discharge shared
callee/caller placement, and compose the guards through actual fetch into the
whole compiler and loop. `ConcreteSimulation` proves computation equivalence
and reachable purity; `ConcreteChanges` proves infinitely many actual changes;
`ConcreteFreshFields` gives the distinct-field witness; `ConcreteTerminalTape`
recovers every halted computation's complete output.
`FiniteExecution` proves exact list-journal execution, one write record per
instruction and unchanged default words outside the journal. `FrozenTM` proves
finite transition-table round trips. `ConcreteFiniteExecution` supplies the
closed finite-data evaluator and outcome equivalence; `FiniteSerialization`
proves its injective integer/natural-list state encoding.
The broader planned layout is:

```text
lean/
  README.md
  PROOF_LEDGER.md
  lean-toolchain
  lakefile.toml
  lake-manifest.json
  SmcTuring.lean
  SmcTuring/
    Specification.lean
    Memory.lean
    Instruction.lean
    Layout.lean
    Purity.lean
    Primitives.lean
    ControlFlow.lean
    Tape.lean
    Simulator.lean
    Simulation.lean
    Universality.lean
    X86/Encoding.lean
    X86/Refinement.lean
    X64/Encoding.lean
    X64/Refinement.lean
    Appendix/Branching.lean
    Appendix/Multiplication.lean
    Appendix/Division.lean
    Examples/Addition.lean
  Challenge.lean
  Solution.lean
  comparator.json
  formalization.yaml
```

The remaining filenames above are a design. The build uses Lean core, Std and
Mathlib pinned to 302343bb9a029d4edab4f737003f0736896c1b64. Both TM adapters and
the TM0-to-SMC composition are checked; the registry package remains pending.
Use the repository's existing `LICENSE.txt` as the starting point for source
licensing metadata; it contains CC0-1.0. The paper has its own published license.

Run `lake build` here with the pinned toolchain installed, or from the repository
root run `python validation/limited_run.py -- python validation/run_lean.py` using the workspace-local installation.
This builds the library and records the theorem axiom audit.
For a fresh checkout, first resolve the locked dependencies and fetch the selected
TM0 and finite-label cache with `python validation/limited_run.py -- python validation/prepare_mathlib.py --update --cache` from the
repository root. Mathlib retains its own Apache-2.0 license.

G95-G96 check the complete native source load and store blocks. Both derive later reader/store setup from the executed guarded address stage and original static placement. The computed pointer is the single active operand shared by load and store. A successful load performs the literal source register update while preserving every other register and heap word; a successful store updates precisely the selected heap word and preserves all registers and other represented heap words. Source register names may alias. Malformed offsets stop after 100 instructions, malformed bases after 222, successful loads after 233 and stores after 239. Exact source outcomes, complete represented-state effects, current-byte traces, code-owned writes, owned-word frames and reusable image/StackTop/SP/CF are checked under explicit cell/no-wrap bounds. N18-N22 close whole emitted role/compiler instantiation under explicit capacity/compactness and source-path bounds. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

Validation uses lakefile.proof.toml with .lake/proof-build, separate from the editor cache. validation/lean_build.py checks that this Lake configuration differs from the canonical lakefile.toml only in buildDir; the package, Lean options, targets and dependency pins are identical. All Lean/native/encoding launchers use that configuration, and both configurations plus the shared launcher and proof audit script are hashed in the evidence. This avoids replacing editor-mapped Windows .olean.private files.

G97-G99 check native program composition, the actual backedge, and lowering of the exact exported 64-MOV kernel. Block readiness is derived from one initial metadata snapshot, physical field separation, the intact image and the actual selected heap pointer; no later trace or Ready is assumed. Finite schedules stop at the literal source trap and preserve all represented source data and code ownership. Successful schedules reach the computed end PC with a reusable invariant; the reset/indirect CALL composes into a closed pass. The kernel layout pass preserves all 64 instruction operands, a common source grid and contiguous encoded PCs. Its address-immediate rejection is explicit: the fixed kernel uses only offset immediates. N18-N22 now derive the complete static placement/metadata certificate from the padded emitter image and prove its full bounded/closed byte pass. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N00-N01 construct the literal inline packet sequences for all source blocks and both shared guards. The exact exported kernel has 1,678 source-body packets, and each guard has 37 inline packets. Physical source/guard positions, finer reader-caller/scalar-entry placement and whole-body embeddings in the padded image are derived from the packet builders. For compiled source schedules, explicit static end-position bounds discharge the conversion from encoded continuations to natural byte positions. N02-N08 now construct that aligned prefix, resolve its addresses and initialize all roles in the complete emitted byte image. N09-N17 derive context consistency, initial reader/scalar readiness, both complete guard certificates, the initial loop invariant and backedge setup. N18-N22 derive every compiled source block's initial Ready, immutable-role frames and the full source-schedule certificate. N23-N27 now construct finite loaded-prefix equivalence. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N02-N08 add 50 checked declarations for aligned templates and finite pools, literal role initialization, native byte lengths, affine metadata separation, the two-pass address allocator and complete byte-image initialization. The exact kernel occupies 9,382 bytes in x86 and 10,816 in x64; guards occupy 206 and 244 bytes. The constructed image contains all 23 shared readers, both guards, source body, backedge and 13 metadata owners; the host observation gap remains unfetched backing bytes. All reader and metadata operands have computed initial values, ownership and alignment, and represented source words initialize correctly in the protected data grid. N09-N17 prove that the source reference context equals this constructed whole and derive the guard and backedge certificates. N18-N22 derive every source block's initial Ready and the full source-schedule Setup. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. `ExportLayout.lean` supplies the allocator's coordinates for an independent finite MASM comparison; that comparison is evidence, not a proof of the Python generator or hardware semantics.


N09-N17 add 76 checked declarations. The fixed compilation now constructs a self-consistent complete byte image; all 23 reader and 13 metadata fit conditions follow from one finite source-grid capacity bound. Metadata fields, reader operands and both guard captures have injective physical and encoded addresses. Literal placed bytes and initialized operands derive reader/scalar/read-update readiness, both complete guard orientations, the initial represented/intact/frame/selected invariant and backedge Setup. Fixed control/register relocations use the explicit compactness condition `heapBase - origin < 2^31`; heap MOFFS operands use full-width capacity bounds. N18-N22 derive its frames across every compiled source block and each block's initial Ready, closing every field of `ProgramImage.Setup`. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. Overall completion remains incomplete.


N18-N22 add 38 checked declarations and close the whole emitted source-schedule certificate. Each block has an actual lowerer witness; its static observations belong to the constructed immutable role set, and that set is disjoint from its complete final-write destinations. All immediate/load/store initial Ready predicates follow from literal placed packets and initialized bytes, with source-register aliasing permitted. `ProgramCertificate.source_setup` supplies every field of `ProgramImage.Setup`; exact entry/end/Linked PCs and a full current-byte/code-owned bounded kernel pass are proved. `closed_pass_correct` composes an accepted pass with the actual backedge and restores the full invariant at kernel entry. Capacity, `heapBase - origin < 2^31`, positive cells and the path's source-address bounds remain explicit. N23-N27 construct finite loaded execution. N43-N55 close the allocation extent bounds. Physical mapping/canonical conditions, coherent hardware fetch, remaining source/appendix proofs and registry packaging remain open. Overall completion remains incomplete.

N23-N27 add 44 checked declarations for finite loaded-memory refinement. A finite byte image stores exactly the loaded interval; its partial evaluator automatically fetches current bytes and accepts only contained header/packet, data-read and full-word-write windows. Loaded-byte agreement preserves all selected scalar effects, write addresses/values, traces and ownership while framing exterior bytes. A computed containing interval supplies safety for every finite fetched prefix without assuming a safe execution. The whole emitted kernel and accepted body plus actual CALL backedge now have constructed finite loaded executions with literal source outcomes and every represented register/heap word preserved. The extent includes the complete represented finite grid. N43-N55 close containment in the prescribed allocation. Physical mapping/canonical conditions, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

[Source inventory and outcome contracts](SOURCE_INVENTORY.md) cover all published
listing groups and distinguish the tested comparison sources, the adapted
construction, intended termination and remaining physical/source obligations.

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

The compact [publishable LaTeX errata](errata/morse-2018-errata.tex) now records the exact M01-M09
local corrections and positive proof justifications. Its location-annotated diff
is checked against twenty published excerpts; `python validation/limited_run.py -- python validation/audit_errata.py`
checks all 53 positive proof references and the two-page PDF. These corrections
are separate from continuing full-paper and physical ISA refinement obligations.

Listing 11 now has 329 checked multiplication declarations: modular arithmetic,
literal data-block effects, actual patched-displacement loop dispatch, all-input
product/termination, input/accumulator restoration, whole-data-trace purity and
exterior-word framing. Its minimally corrected literal x86 fixture passes
11,458 cases. E34-E36 complete selected word/register CALL/ESP and actual-PC loop composition. E37-E40 add the exact missing byte forms, finite-field refinement and all 55 literal packets plus four inactive owners. Native comparison checks all 422 bytes, fourteen fields and 57 address relocations. E41-E45 construct the original image, derive all fourteen code owners and build actual current-byte traces/invariant/refinement for each data block. E46-E49 derive original operands/stack/CALL setup and complete live-byte blocks, including arithmetic-derived control targets/endpoint PCs, owned writes and finite field refinement. E50-E52 close the entire original-image actual-PC/current-byte loop, product, registers/inputs, owned writes and exact original exterior-byte frame outside ten scratch/result fields. E03 is checked for the selected byte machine; physical ISA/configuration/fetch remains E05.
See [the multiplication scope](APPENDIX_MULTIPLICATION.md).


Listing 6's constant emitter now has all-input arithmetic and complete compiled
word-trace proofs, including signed patterns, zero, legal SHL counts, restored
EAX, code-write purity and the exterior-word frame. The native reconstruction
passes 54,366 x86 runs and an independent Lean comparison of all 11,350 emitted
pure packets. [APPENDIX_CONSTANT_MULTIPLICATION.md](APPENDIX_CONSTANT_MULTIPLICATION.md)
gives the exact M08 local correction and remaining byte/auxiliary obligations.


E56-E62 add 99 positive byte-codec/effect/refinement/image/current-fetch results
for that constant emitter. `ConstantSimulation.original_image_correct` proves
an actual live-byte trace, product, EAX/ESP restoration, code-write ownership
and exact exterior-byte frame from one original image and static complete
placement/own-immediate/ownership/capacity facts. Deriving those static facts
for the complete variable-length emitter is the next bridge. All 11,350 pure
native packets now match the actual checked Lean byte codec and owner offsets.
The full audit records 2,681 declarations and complete multiline axiom lists.


E63-E66 close the whole constant-emitter geometry bridge with 44 further
checked results. `ConstantCorrect.correct` proves the complete live-byte
execution/effects/frame from only original initialization, entry and full image
capacity; every static packet/operand/ownership identity is constructed.
`reusable_correct` covers arbitrary current data and scratch from the retained
image invariant. Native comparison now checks actual Lean-computed coordinates,
complete owner packets and pure packets, retaining 54,366 cases and 79,534
original-image bytes. The audit has 2,725 declarations/301 unique ledger IDs;
184 belong to the constant-emitter chain. Auxiliary Listing 6 operations,
division and the remaining literal/physical/registry gates retain scope.


E67 closes Listing 6 DEFZERO's complete live-byte zeroing and re-entry contract
with 18 positive proofs. M09 keeps one XOR and selects the intended complete
DWORD immediate with explicit typing and existing CNSTFRC32. Its corrected
macro passes 9,312 executions per architecture and actual MASM/Lean packet
comparison. The compact errata remains two pages, now with 20 exact excerpts
and 53 audited positive references. The audit has 2,743 declarations and 302
ledger IDs. See [APPENDIX_ZERO.md](APPENDIX_ZERO.md); conversions and template
copying remain the next E01/P04 work.

E68-E72 close full-width Listing 6 USEWORD conversion with 53 positive
current-byte proofs, source/full AX/SP/CF restoration, exact exterior bytes,
reusable helper, patched operand decoding and original-image code-owned copying.
Finite native tests pass 21,792 x86 and 24,912 x64 executions across six layouts;
all helper and owner packets match the actual Lean codec. The full audit has
2,796 declarations/307 ledger IDs. See [APPENDIX_CONVERSION.md](APPENDIX_CONVERSION.md).
Whole-template copying/relocation remains the next E01/P04 step. The compact
M01-M09 errata remains two pages with 20 excerpts/53 correction proofs.

E73-E77 add 51 positive byte-copy/literal-plan/cursor/unified-memory/codec
contracts for Listing 5. M10 keeps the copy algorithm and corrects six cursor
operands, plus the example labels and explicit forward-copy preconditions.
Native x86/x64 each pass 6,144 executions/48 sizes, and every complete macro
matches Lean (3,762/5,682 bytes and 96 cursor fields per architecture). The full
audit has 2,847 declarations/312 ledger IDs. The exact 28-excerpt minimal diff
and 59 positive correction references remain a clean two-page errata.
See [APPENDIX_TRANSFER.md](APPENDIX_TRANSFER.md); whole macro live-fetch and
copied-template relocation/decoding remain P04.

E78-E82 extend the actual codec/fetch with SI/DI, MOVS and immediate SUB, prove
the complete initialized MOVS body's actual-byte trace and word-index copy
contract, and check copied-packet decoding plus internal RIP/external absolute
reference laws. All complete native macro packets pass live Lean decoding.
See [APPENDIX_TRANSFER.md](APPENDIX_TRANSFER.md). Complete macro stage composition
and whole-template absolute/MOFFS patching remain P04.

E83-E90 add the actual initializer/prefix/restoration traces and complete
emitted-program encoding with 50 further results. The initializer's pointed
word comes from its original bytes; the exact prefix loads source/destination
and saves arbitrary old SI/DI in the declared fields. Restoration fetches and
CF=false are derived from static placement/capacity. Full macro trace/state
composition remains P04; see [APPENDIX_TRANSFER.md](APPENDIX_TRANSFER.md).

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
errata remain unchanged. Refresh with `python validation/limited_run.py -- python validation/run_template.py` after
the Lean audit and before the aggregate evidence audit. Other branch geometries, literal Listing 8/9/finalization/half-field placements,
physical ISA/fetch and registry gates retain their full scope.

`TemplateCopy.original_addresses_correct` joins every live destination fetch
with its exact natural address meaning. Static `ReferencesValid` supplies
per-packet signed reach and full target capacity; these are compiled-layout
properties, not future address-hit or execution assumptions.

The complete audit has **3,496** declarations and **370** unique ledger IDs.
E121-E131 add **170** positive byte-layout/execution declarations, and E116
adds the common-byte run bridge. E132 checks that the constructed original
image, its actual owner fields and six placement premises match all four
native layouts.

`DivisionByteCorrect.correct` now constructs the entire continuous current-byte
execution from one original emitted image, entry PC, static ordered placement/
capacity bounds and nonzero inputs. It proves all four quotient/remainder
results, exact CF, input/EAX/ESP restoration, endpoint PC, zero displacement,
only code-owned DWORD writes and every original byte outside the actual
scratch/result fields. `reusable_correct` derives another complete invocation
from the maintained image/stack/reset and current inputs with arbitrary scratch
values. Signed quotient truncates toward zero, excluding MIN_INT/-1 only for
an in-range integer quotient; the remainder theorem includes that case.

Native regression passes **52,648** executions. All **344** unique packets,
**2,532** complete bytes, **333** DIR32 sites and **91** mode-owned fields match
actual Lean, including the constructed whole original image. E04 is checked
for the selected finite x86 byte machine. Physical ISA/configuration/coherent
fetch, remaining literal source/x64 placements and
review-package gates retain their full scope. M01-M11, 33 exact excerpts,
70 positive errata references and the compact two-page TeX/PDF are unchanged.

The complete branch theorem now also permits all disjoint region orders and
backward targets (E133-E134). Ten static checks derive the entire current-byte
trace, actual target/endpoint, input/EAX/ESP/CF, owned writes and original-byte/
gap frame. E135 passes all 24 orders/288 layouts/144 backward targets/1,785,600 native
executions, with 8,112 full packets/2,016 owner fields/8,112 DIR32 sites matching
Lean;
see [the branch geometry record](APPENDIX_BYTE_SPACING.md). The audit has 3,496 declarations and
370 ledger IDs. Remaining literal source/x64 placement, physical ISA/fetch and
review-package gates retain their scope; the compact errata is unchanged.


## Terminal marker checkpoint - 2026-10-06

E136-E138 close the local corrected Listing 2 DOHALT contract. Twenty-seven
positive declarations check its full ten-byte current packet, x86 absolute/x64
RIP-relative self-immediate store, PC advance, AX/SP/CF, unchanged whole memory
and every output window, reusable encoding and nonempty code-owned writing.
Each architecture passes 4,128 typed-original and 4,128 corrected executions;
all GPRs/SP/status flags, endpoint, adjacent code bytes and unchanged-live-image
reentry are checked. Complete loaded and object bytes match actual Lean,
including x86 DIR32 and x64 REL32_4 symbols/addends.

M12 makes one destination-offset/type correction and one observation sentence;
the existing algorithm and instruction length are retained. The immediately
updated exact diff and visually verified two-page TeX/PDF contain M01-M12,
35 original excerpts and 74 local positive references. The evidence paragraph
now cites the completed whole division proof. See [the terminal correction
contract](APPENDIX_TERMINAL.md).

This checkpoint supersedes the preceding audit totals: 3,523 declarations and
373 unique ledger IDs. All twelve native suites, the encoding/errata checks and
the aggregate evidence audit pass. P07 now records the checked local marker;
literal Listing 8/9 final-state composition, x64 half-field placement, physical
ISA/configuration/fetch and review-package gates retain their full scope.
The full-paper goal remains active.


## Accumulator/finalization checkpoint - 2026-10-06

E139-E143 prove Listing 9's unchanged four-instruction full-width sequence and
its composition with an actual body trace and corrected terminal. Forty-nine
positive declarations derive the static addresses/PCs, prologue save and original
pointer bytes, exact epilogue memory/AX/SP/CF, code-owned writes, current-byte
fetches after prior stores, output frames and live reuse. The body may change
AX and arbitrary output; its save/pointer reserved words and current marker
must satisfy the stated boundary contract. Future epilogue/terminal fetches are
derived. Literal Listing 8 must still establish that body contract.

Each architecture passes 38,400 executions over six save/pointer/body-owner
orders, forty boundary/random full-width entry/body words, both CF and two
unchanged-image consecutive calls. The pure body produces an independently
checked full-word output. All GPRs/SP/status flags, full AX (including upper RAX),
outputs, endpoint, reserved reset and every exterior code byte are checked.
All 72 loaded/object packets, 54 relocations and complete owner widths match
actual Lean: 408 x86 or 594 x64 bytes, with RIP REL32, terminal REL32_4 and
full-width x64 ADDR64 where appropriate.

This checkpoint supersedes earlier totals: **3,572 audited declarations** and
**378 unique ledger IDs**. All thirteen native suites, encoding/errata checks
and aggregate evidence audit pass. No new paper erratum was established;
M01-M12, the 35-excerpt minimal diff, 74 local positive references and two-page
TeX/PDF are unchanged. Full-width storage-owner placement is explicit. Optimized
DEFDATA32/native x64 half fields, the literal Listing 8 body, physical realization
and review-package work retain their scope. See [the accumulator and finalization
contract](APPENDIX_ACCUMULATOR.md). The full-paper goal remains active.


## Input-symbol operand checkpoint - 2026-10-06

E144-E145 close the local positive M13 correction: add only IMMOFFS to the
source operand of Listing 8's inputupdate USEWORD32 call. Fifteen declarations
derive the symbol from COMPARE32's current immediate at offset six and all
patched XOR target bytes at offset three. The original three instructions
retain source/AX/SP/CF, code-write purity, complete source/header and exterior
byte frames. The universal current-byte helper theorem uses the selected x86
model; the logical DWORD contract holds in either mode.

Each architecture passes 6,400 corrected and 6,400 typed-original executions
over forty entry words, forty live symbols, both CF and consecutive reuse.
Expected x64 low-AX zero extension, all GPRs/SP/status flags, source restoration,
target symbol, endpoint and every exterior byte are checked. All twelve loaded/
COFF packets and ten relocations per architecture match actual Lean: 88 x86 or
90 x64 bytes, including long-mode REL32_4.

This checkpoint supersedes previous totals: **3,587 audited declarations** and
**380 unique ledger IDs**. All fourteen native suites, encoding/errata checks
and the aggregate evidence audit pass. The immediately updated M01-M13 exact
diff and visually verified two-page TeX/PDF contain **36 published excerpts**
and **79 local positive proof references**. See
[the positive input-symbol contract](APPENDIX_INPUT_OPERAND.md) and
[the literal Listing 8 completion plan](APPENDIX_LISTING8_PLAN.md).

Full literal Listing 8 composition, its storage/node initialization, universal
long-mode DWORD byte execution and optimized field placement, physical ISA/
configuration/fetch and the review package retain their scope. The full-paper
goal remains active.


## Live DWORD scalar checkpoint - 2026-10-06

E146-E147 establish M14 with seventeen positive both-mode current-byte proofs
and complete native packets. The only paper change is the one call
DEFDATA(0, curtinputval) to DEFDATA32(curtinputval,0), using the already defined
primitive and its label/value order. The four-byte field at offset six matches
both consumers. Initial zero, complete current packets after arbitrary live
patches, actual self-store, PC, full AX/SP/CF, whole-memory/output preservation,
nonempty code writing and reuse are proved. The live candidate is retained.

Each architecture passes 6,400 cases over forty full-width entry words and forty
DWORD symbols, both CF and consecutive unchanged-image calls. All GPRs/SP/status
flags, full AX, endpoint, live scalar and complete packet bytes are checked.
Forty live packets and the zero initializer (410 bytes per mode), plus the
complete COFF packet and DIR32/REL32_4 relocation, match actual Lean.

This checkpoint supersedes earlier totals: **3,604 audited declarations** and
**382 unique ledger IDs**. All fifteen native suites and encoding/errata/
aggregate provenance checks pass against the same proof snapshot.
M01-M14 have **37 exact source excerpts and 83 positive local proof references**;
the exact diff and visually checked publishable TeX/PDF were updated immediately
and remain two pages. See [the positive scalar contract](APPENDIX_DWORD_OWNER.md).

The local scalar declaration is resolved. Full literal Listing 8 setup,
comparison/input update, node/state selection, backedge and finalization, the
universal x64 DWORD helper, optimized field placement, physical ISA/configuration/
fetch and the review package retain their remaining gates. The goal remains active.


## Both-mode DWORD helper checkpoint - 2026-10-06

E148-E153 add 77 positive declarations and close the universal x64 DWORD
exchange/store gap. Exact bare encodings and opcode-derived current fetch,
four-byte natural-address memory effects, actual six-byte RIP ends, original
source restoration, target-only change, SP/CF, unchanged x86 EAX and correctly
zero-extended RAX are proved. The finite original byte image derives every
later helper fetch after preceding stores and remains reusable.

InputDword.copy_correct derives the live source symbol and complete target
XOR packet in both modes; source/code/header/exterior frames and all three
nonempty code-field writes follow. Nine executable static checks are proved
equivalent to admissibility. Native comparison now uses these actual model
encodings and checks every premise. Each architecture passes 6,400 corrected
and 6,400 typed-original cases, all twelve loaded/COFF packets (88/90 bytes),
ten relocations and complete GPR/SP/status-flag/endpoint/byte/reuse checks.
Actual x64 PCs and source/target addresses are above 4GiB.

This checkpoint supersedes earlier totals: **3,681 audited declarations** and
**388 unique ledger IDs**. All fifteen native suites, encoding/errata checks
and aggregate provenance pass against the same proof snapshot.
No new paper correction is introduced: M01-M14, 37 exact excerpts and 83
positive errata references remain. The visually checked two-page TeX/PDF now
cites the stronger both-mode proof. See
[the DWORD helper contract](APPENDIX_DWORD_COPY.md).

Full literal Listing 8 comparison/input update, node/state initialization,
backedge/finalization and optimized storage placement, physical ISA/
configuration/fetch and review-package gates remain. The next step composes
the proved M13/M14 contracts with COMPARE32 and the conditional input update.
The goal remains active.


## DWORD comparison and selection checkpoint

E154-E157 add 53 positive declarations: 19 for the eight actual DWORD arithmetic
forms, 24 for the packed comparison image/effects/current trace/purity/static
checks and 10 for conditional input selection and the final base-addressed
DWORD tape XOR step. The equality mask and selected tape symbol are proved for
all DWORDs in both modes, with exact AX/SP/CF/PC and exterior byte frames.

Each native packed comparison fixture passes 51,200 cases/1,280 matches,
41 complete comparison images plus two owner packets (1,619 bytes), seven COFF
relocations and eleven proved static checks. Independent scalar/mask/full
GPR/SP/status-flag/endpoint/code-frame/repeated-invocation checks pass; actual
x64 code/scalar/mask addresses are above 4 GiB.

This checkpoint supersedes earlier totals: **3,734 audited declarations** and
**392 unique ledger IDs**. All sixteen native suites, encoding/errata checks
and aggregate provenance pass against the same proof snapshot. Only the
permitted standard axioms occur. M01-M14, 37 exact excerpts, 83 positive errata
references and the visually checked two-page TeX/PDF are unchanged.
See [the DWORD comparison and selection contracts](APPENDIX_DWORD_COMPARISON.md).

The packed comparison places reset immediately before SUB; printed Listing 8
interleaves the separately proved M13 copy and M14 owner. Compose those actual
instructions next, then the preceding XOR/AND patches and both full-width
cursor exchanges. Full node/direction/state initialization, backedge/finalization,
optimized storage placement, physical ISA/configuration/fetch and review-package
gates remain. Core unbounded universality/output/converse proofs stay checked.
The goal remains active.
