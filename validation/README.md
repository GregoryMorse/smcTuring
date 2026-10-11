# Reproducible validation

**Current final policy (2026-10-10):** full Linux kernel/axiom evidence plus actual Windows native/assembler CI are the completion gates. Full Windows Lean and resource-only refactors are optional. See [portable pinned CI](ci/README.md). Native jobs retain the existing 1.5 GB guard; the Linux parent scope and all pins stay unchanged. Historical commands below retain their original local scope.


**Current verification policy (2026-10-06):** Lean is pinned to
`leanprover/lean4:v4.35.0-rc3`, commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`.
Run every build/test command serially through `validation/limited_run.py`.
Windows caps aggregate committed allocation at 1.5 GB; a 25 ms monitor also
stops the job at a conservative 1.5 GB resident threshold. Direct Lean uses
`-M768 -j1`. Never retry a capped failure without the guard.
The newer cursor fragment has a separate 63-declaration local audit and native packet binding.
The prior 3,734-declaration/sixteen-native-suite snapshot is historical;
the changed worktree's whole-library audit remains pending.


Run these commands from the repository root on Windows with Visual Studio C++
and MASM installed. The shared launcher normalizes Windows environment names
so Visual Studio's `Path` replaces inherited `PATH`; the native report hashes
that launcher as well as the fixture sources:

```powershell
python validation/limited_run.py -- python validation/prepare_mathlib.py --update --cache
python validation/limited_run.py -- python validation/run_baseline.py --as-of 2026-10-03
python validation/limited_run.py -- python validation/run_defaddr.py
python validation/limited_run.py -- python validation/run_lean.py
python validation/limited_run.py -- python validation/run_pure.py
python validation/limited_run.py -- python validation/audit_encoding.py
python validation/limited_run.py -- python validation/audit_evidence.py
```

`run_baseline.py` rebuilds the unchanged C++/MASM source in Debug/Release on
Win32/x64, supplies a newline for the driver's final `getc`, and checks every
simulator output. It preserves source and executable hashes plus build commands.
The first passing run is [baseline.json](baseline.json); the requested retest
after the macro repair is [baseline-after-repair.json](baseline-after-repair.json).
All four configurations and all 30 outputs passed in each run.

`run_defaddr.py` assembles the published and corrected macro definitions from
[pure_smc.inc](../smcTuring/pure_smc.inc), executes both on x86/x64, and checks
the returned accumulator, restored pointer field, and restored target word.
The deterministic suite includes edge words and pseudorandom values, with both
separate targets and exact self-aliasing. [defaddr.json](defaddr.json) records
20,324 passing cases per architecture. The host setup and return are excluded
from the four-instruction purity claim. Writable executable code is enabled in
this test fixture; partially overlapping word fields are not tested.

`run_lean.py` uses the repository-local toolchain named by `lean/lean-toolchain`.
Install it with Elan using `ELAN_HOME` set to `lean/.elan`, or adapt the launcher
to a separately installed identical toolchain. The script builds the library,
checks its theorem axiom report against the three allowed standard axioms, and
checks proof sources for admitted declarations. [lean.json](lean.json) records
the exact toolchain commit, public theorem audits, and source hashes.

The audit covers 3496 declarations: the DEFADDR repair, Dolan's fixed 64-MOV
scanner and its four-register compilation, the constructed pure SMC word image,
finite-input initialization, guarded compiler and actual backedge, and TM
halting/nonhalting equivalence. It also checks complete terminal tape/head
recovery, arbitrarily late actual code changes, an explicit distinct-field
unboundedness witness, and finite-data journal execution with reversible state
encoding. The actual pinned Mathlib TM0 compiler preserves its partial-evaluation
domain and complete relative tape through the SMC construction. The reverse
adapter covers arbitrary source blank/start values, three finite labels per
source state and two actual TM0 steps per transition, with halting/output
correspondence. Primitive-recursion certificates cover the finite journal,
signed arithmetic/comparison/borrow, bitwise operations, the state codec,
all instruction effects, operand resolution and the actual fixed-image header lookup.
Finite machine descriptors, the actual initial-word generator and the complete
bounded evaluator also have primitive-recursion certificates and exact semantic
contracts. The unbounded search and actual TM2/TM1/TM0 composition now have
checked partial evaluation, finite support, positive progress and complete
terminal-journal recovery. Literal finite-label restriction and blank/start-
preserving numbering now compose with the source/SMC adapters, closing T13.
The exact repository addition example is kernel reduced for 132 transitions,
with a genuine halt, head 10 and `1101_0000_`; its complete terminal tape/head
and pure SMC realization are checked. Selected instruction encoding, byte patch/current
fetch and affine grid geometry are checked in G58-G61. G62 additionally checks
finite-word guard arithmetic and indexed pointers under capacity bounds; CPU
refinement remains open. G63 checks the selected non-faulting execution
projection, including decoded-trace CF preservation, aliased CALL pushes and
execution of newly patched MOFFS addresses. G64 adds opcode-derived automatic
current-byte fetch, including CF/SBB bridges without a supplied packet length.
G65 checks every selected complete write and all four byte reader effects,
full memory restoration, SP/CF preservation and owned write destinations.
Live final-packet safety covers exact self-alias or complete-packet separation.
G66-G67 additionally check code-backed SP reset/CALL, reusable StackTop,
complete shared-reader callee and caller/callee return/memory/CF contracts.
Automatic-fetch traces and owned write properties compose at the reached state.
G68 constructs the concrete register/heap byte storage grid, proves exact
initial values and owner opcodes, and preserves every opcode through actual
owned-write traces. Current MOFFS operands and bounded encoded-address load
agreement are checked. G69-G70 construct finite control/metadata packets and a
combined control/grid image, with computed separation, exact initialization and
preservation of both regions through owned-write traces. G71 derives the placed
reader's addresses, all four automatic fetches, owned writes and exact initial
grid load. G72 checks signed rel32 extension and computed absolute/RIP/CALL targets,
including backward transfers and SBB's complete size.
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
contribute 30 audited declarations. Remaining whole role/compiler
instantiation and hardware region/fetch refinement remain open.
Whole generated-kernel role layout, guard/source/compiler simulation,
applied address/relocation bounds and hardware validity/fetch remain open.

`prepare_mathlib.py` resolves revision
`302343bb9a029d4edab4f737003f0736896c1b64` and its eight locked transitive packages.
It checks the compatible toolchain and downloads the TM0, finite-label and primitive-recursion cache closures.
[mathlib.json](mathlib.json) records primary metadata and source hashes.
`run_lean.py` also hashes the project configuration, imported TM/primitive-recursion sources and
the pinned Lean natural-number bitwise, BitVec, division and list-ofFn implementations.
`audit_evidence.py` checks those pins and hashes, unique declaration/ledger IDs,
native proof provenance and the checked encoding/arithmetic/execution/automatic-fetch/reader/call/callee/storage-grid/combined-image/placed-reader/relocation/fragment-view/placed-call/placed-callee/read-invocation/store-callee/store-invocation/padded-image/ALIGN/scalar/borrow-mask declarations. The launcher decodes Lean's output as UTF-8 on Windows.

`run_pure.py` exports the checked 64-MOV kernel using `lean/ExportKernel.lean`
and generates both MASM implementations. [pure.json](pure.json) records 109
scenarios, 535 observed body passes and 107 genuine closed-loop computations
per architecture. Every logical register and every word of the 4,096-cell heap
is compared with a separate MOV interpreter after each observed pass; terminal
cases are rerun without host observations between passes. Independent TM
examples check head/tape results: original addition output `1101_0000_`,
empty/missing transition tables, matching/nonmatching candidates, both directions
beyond input, 48-step closed loops and bounded nonhalting runs. Random source
states exercise aliases and invalid word tags.

The linked fixture checks aligned, disjoint `A3`/`48 A3` operand ownership,
the affine register/heap field layout and disabled CET shadow stacks. Setup,
cache flushing and host observation are outside the computational boundary.
Code pages are writable/executable; Windows executable copy-on-write mappings
are accepted. The kernel uses accumulator/SP scratch and code-backed CALL
returns. Native tests have a finite capacity premise and do not prove
fixed-width unbounded computation. See [architecture notes](../lean/ARCHITECTURE_NOTES.md).

`fetch_intel.py` caches the pinned revision-093 primary manuals;
[intel-manuals.json](intel-manuals.json) records URLs and SHA256 values.
`audit_intel.py` extracts complete selected instruction entries, including
ordinary MOV and Volume 2D XCHG/XOR, for review. These are source evidence,
not Lean ISA proofs.

Build output, disassembly, MASM listings, and downloaded source PDFs are ignored
under `.build/` and `.cache/`. The JSON reports are reviewable source artifacts.
They record actual finite tests and kernel checking. The full byte/CPU
refinement and the remaining source/appendix/ancillary gates remain pending.

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

See [encoding.json](encoding.json).

G93 checks the 33-instruction pointer construction: the base and offset are read from represented source registers, added in the single active load/store operand, then copied through the PointerWord reader into Candidate. Source-register aliases are allowed; all represented data and other owned metadata are preserved. G94 composes both guards and this pointer stage from original-memory setup. A malformed offset stops after 100 instructions; a valid offset reaches the Base guard after 222. The continuation is chosen exactly when the literal source address succeeds, and its selected heap word is left in the shared operand. Current-byte traces, code-owned writes, frames for other owned words outside the seven written fields, source-data preservation and reusable image/StackTop/SP/CF are checked. Remaining emitted role/compiler instantiation, applied bounds and hardware region/fetch refinement remain open.

G95-G96 check the complete native source load and store blocks. Both derive later reader/store setup from the executed guarded address stage and original static placement. The computed pointer is the single active operand shared by load and store. A successful load performs the literal source register update while preserving every other register and heap word; a successful store updates precisely the selected heap word and preserves all registers and other represented heap words. Source register names may alias. Malformed offsets stop after 100 instructions, malformed bases after 222, successful loads after 233 and stores after 239. Exact source outcomes, complete represented-state effects, current-byte traces, code-owned writes, owned-word frames and reusable image/StackTop/SP/CF are checked under explicit cell/no-wrap bounds. N18-N22 close whole emitted role/compiler instantiation under explicit capacity/compactness and source-path bounds. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

Validation uses lakefile.proof.toml with .lake/proof-build, separate from the editor cache. validation/lean_build.py checks that this Lake configuration differs from the canonical lakefile.toml only in buildDir; the package, Lean options, targets and dependency pins are identical. All Lean/native/encoding launchers use that configuration, and both configurations plus the shared launcher and proof audit script are hashed in the evidence. This avoids replacing editor-mapped Windows .olean.private files.

G97-G99 check native program composition, the actual backedge, and lowering of the exact exported 64-MOV kernel. Block readiness is derived from one initial metadata snapshot, physical field separation, the intact image and the actual selected heap pointer; no later trace or Ready is assumed. Finite schedules stop at the literal source trap and preserve all represented source data and code ownership. Successful schedules reach the computed end PC with a reusable invariant; the reset/indirect CALL composes into a closed pass. The kernel layout pass preserves all 64 instruction operands, a common source grid and contiguous encoded PCs. Its address-immediate rejection is explicit: the fixed kernel uses only offset immediates. N18-N22 now derive the complete static placement/metadata certificate from the padded emitter image and prove its full bounded/closed byte pass. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N00-N01 construct the literal inline packet sequences for all source blocks and both shared guards. The exact exported kernel has 1,678 source-body packets, and each guard has 37 inline packets. Physical source/guard positions, finer reader-caller/scalar-entry placement and whole-body embeddings in the padded image are derived from the packet builders. For compiled source schedules, explicit static end-position bounds discharge the conversion from encoded continuations to natural byte positions. N02-N08 now construct that aligned prefix, resolve its addresses and initialize all roles in the complete emitted byte image. N09-N17 derive context consistency, initial reader/scalar readiness, both complete guard certificates, the initial loop invariant and backedge setup. N18-N22 derive every compiled source block's initial Ready, immutable-role frames and the full source-schedule certificate. N23-N27 now construct finite loaded-prefix equivalence. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open.

N02-N08 add 50 checked declarations for aligned templates and finite pools, literal role initialization, native byte lengths, affine metadata separation, the two-pass address allocator and complete byte-image initialization. The exact kernel occupies 9,382 bytes in x86 and 10,816 in x64; guards occupy 206 and 244 bytes. The constructed image contains all 23 shared readers, both guards, source body, backedge and 13 metadata owners; the host observation gap remains unfetched backing bytes. All reader and metadata operands have computed initial values, ownership and alignment, and represented source words initialize correctly in the protected data grid. N09-N17 prove that the source reference context equals this constructed whole and derive the guard and backedge certificates. N18-N22 derive every source block's initial Ready and the full source-schedule Setup. N23-N27 construct finite loaded-prefix refinement. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. `ExportLayout.lean` supplies the allocator's coordinates for an independent finite MASM comparison; that comparison is evidence, not a proof of the Python generator or hardware semantics.

The current assembler audit also executes `lean/ExportLayout.lean` and compares
its computed section positions against MASM: 23 reader entries and operands,
13 metadata operands, both guard entries and capture operands, all 64 source
block boundaries, kernel/backedge/observation positions and register/heap grid
bases. Both architectures match. The excluded host-stub extent and fault offset
are verified explicitly as allocator inputs. `computed_layout_checked` and the
exact exported coordinates are recorded in `encoding.json`. This finite
comparison does not establish CPU fetch coherence or a whole-schedule Ready
certificate.


N09-N17 add 76 checked declarations. The fixed compilation now constructs a self-consistent complete byte image; all 23 reader and 13 metadata fit conditions follow from one finite source-grid capacity bound. Metadata fields, reader operands and both guard captures have injective physical and encoded addresses. Literal placed bytes and initialized operands derive reader/scalar/read-update readiness, both complete guard orientations, the initial represented/intact/frame/selected invariant and backedge Setup. Fixed control/register relocations use the explicit compactness condition `heapBase - origin < 2^31`; heap MOFFS operands use full-width capacity bounds. N18-N22 derive its frames across every compiled source block and each block's initial Ready, closing every field of `ProgramImage.Setup`. The model's allocation bounds are closed through N55; hardware mapping/canonical conditions and coherent fetch remain open. Overall completion remains incomplete.


N18-N22 add 38 checked declarations and close the whole emitted source-schedule certificate. Each block has an actual lowerer witness; its static observations belong to the constructed immutable role set, and that set is disjoint from its complete final-write destinations. All immediate/load/store initial Ready predicates follow from literal placed packets and initialized bytes, with source-register aliasing permitted. `ProgramCertificate.source_setup` supplies every field of `ProgramImage.Setup`; exact entry/end/Linked PCs and a full current-byte/code-owned bounded kernel pass are proved. `closed_pass_correct` composes an accepted pass with the actual backedge and restores the full invariant at kernel entry. Capacity, `heapBase - origin < 2^31`, positive cells and the path's source-address bounds remain explicit. N23-N27 construct finite loaded execution. N43-N55 close the allocation extent bounds. Physical mapping/canonical conditions, coherent hardware fetch, remaining source/appendix proofs and registry packaging remain open. Overall completion remains incomplete.

N23-N27 add 44 checked declarations for finite loaded-memory refinement. A finite byte image stores exactly the loaded interval; its partial evaluator automatically fetches current bytes and accepts only contained header/packet, data-read and full-word-write windows. Loaded-byte agreement preserves all selected scalar effects, write addresses/values, traces and ownership while framing exterior bytes. A computed containing interval supplies safety for every finite fetched prefix without assuming a safe execution. The whole emitted kernel and accepted body plus actual CALL backedge now have constructed finite loaded executions with literal source outcomes and every represented register/heap word preserved. The extent includes the complete represented finite grid. N43-N55 close containment in the prescribed allocation. Physical mapping/canonical conditions, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N28-N35 add 38 checked declarations for bounds in one allocation fixed by the emitted layout and requested finite source grid. Every placed control entry has a contained fifteen-byte fetch window; complete metadata, register, selected heap and all 23 initial reader-pointer words are contained, and the allocation fits the finite machine address space. Initial pointer/StackTop values and actual executed-state frames derive bounds for the repaired reader, reset/CALL, seven-instruction callee, ten-instruction caller round trip, each scalar operation and eleven-instruction read/update. Literal initialized placed callers and read/update fragments therefore have finite loaded executions in this prescribed allocation. N36-N42 compose the guards; N43-N55 complete the dynamic source and whole-kernel allocation certificate. Canonical-address validity, permissions/segmentation/CET, coherent hardware fetch, source/appendix audits and registry packaging remain open. Overall completion remains incomplete.

N36-N42 add 22 checked declarations composing the fixed-allocation bounds through all guard stages. Static packet placement derives reader/callee/scalar/CALL fetch windows from one control interval. Proved pointer frames derive every data-read and complete word-write bound through the 26-instruction capture/setup, 13-instruction borrow-mask and 47-instruction selector/return stages. Both 86-instruction guard orientations and the actual 89-instruction outer invocation have finite loaded executions in the preselected allocation, derived from the initialized emitter image, capacity/compactness and typed metadata; no future safe trace or intermediate Ready is supplied. N35 additionally proves containment of the whole static control interval, bringing its declaration count to 19. N43-N55 close the remaining dynamic source and whole-kernel allocation bounds. Physical canonical/permission/segment/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.

N43-N55 add 31 checked declarations closing dynamic source and whole-kernel bounds in the allocation fixed before execution. Pointer construction reads contained register and operand words without dereferencing an unvalidated value. Successful load/store operands are proved equal to the selected contained heap word from source representation and finite-cell bounds; rejected tag paths execute their contained guards. All actual compiled blocks obtain static certificates from their literal lowerer witnesses. Schedule induction derives current Ready from the preserved invariant at every boundary, then composes the complete emitted body and actual reset/indirect CALL backedge. `ProgramAllocation.kernel_loaded` and `closed_loaded` construct their finite loaded executions with exact source outcomes, every represented register/heap word, code-owned writes and the closed entry PC. No future safe trace, intermediate Ready or trace-dependent allocation extent is supplied. Address-space capacity, compact relocations, positive cells and source-path cell bounds remain explicit. Physical mapping, canonical/segment/permission/CET/current-fetch conditions, literal source/appendix gates and registry packaging remain open. Overall completion remains incomplete.

The Y02 split-word audit checks 22 `X64/HalfWords` declarations. These include
full-word Boolean/assignment identities, repeated-immediate semantics, direct
carry/borrow arithmetic proofs and concrete boundary counterexamples. They are
included in the full root import, standard-axiom audit and evidence inventory.
This adds a value-level proof; it changes no emitted native fixture or original
comparison source. Literal half-field, exchange/frame and flag contracts remain
separate paper obligations (M04 in `lean/ERRATA.md`).

The printed Listing 10 predicate and displacement-patching prefix has 39
checked field-word declarations in `Appendix/Machine32`, `BranchAlgebra` and
`Branching`. All six signed/unsigned relations, exact restoration/full-memory/CF
frames, actual mutable operand selection, modular target, conditional code writes
and an alias counterexample are in the standard-axiom audit. Byte owners/fetch,
E20-E24 now close reference byte-level stack/CALL execution and continuation IP;
general host spacing and physical ISA/fetch remain open. E09
checks the word/register tail and restoration alias, E10 supplies whole native
branch tests, and E11 checks the packet codec and live operand patches.
See `lean/APPENDIX_BRANCHING.md` and M05 for the source contract.

Run `python validation/limited_run.py -- python validation/audit_appendix_calls.py` before the final
`python validation/limited_run.py -- python validation/audit_evidence.py`. The three-way x86 MASM comparator verifies
that the literal bracketed NEAR-code-label CALL is E8 rel32 with field +1,
while explicit DWORD PTR forces FF /2 with field +2. This is finite typing/
encoding evidence only. The final evidence audit checks its source, paper and
object/listing hashes as well as the three expected packets.

E09 additionally checks 23 declarations for the printed x86 single-XCHG/CALL
and JUMPTARGET word/register effects, including the real return-slot/MOV-address
alias and composition with all signed/unsigned branch predicates. Exact boundary
words and ESP are restored; nonwrapping continuation ADD gives CF=false.
E15-E24 close reference byte owners, current fetch, tail/continuation and both
end PCs. General host spacing and physical ISA/fetch remain open; E10 now supplies whole native branch tests and E11 supplies packet patch/fetch proofs. See `lean/APPENDIX_BRANCHING.md` for the precise scope and assumptions.

E10 supplies 74,400 normalized whole x86 branch cases across all 12 relations,
with exact GPR/ESP/CF/owner-word and other-code-byte checks. E11 adds 24 kernel
packet codec/current-patch proofs; 13 Lean encoding exports are compared directly
with 338 MASM headers, 84 actual fields and 338 symbol-target relocations.
E12-E14 now establish selected byte effects and finite field-word prefix
refinement. E15-E24 close reference own operands, headers, continuous live fetch and
byte tail/continuation composition. General host spacing and physical ISA/fetch
remain open. See `../lean/APPENDIX_BYTE_CODE.md` for the precise contract.

Reproduce this branch milestone with `python validation/limited_run.py -- python validation/run_branch.py` after
`python validation/limited_run.py -- python validation/run_lean.py`, before `python validation/limited_run.py -- python validation/audit_evidence.py`.
The x86-only Listing 10 fixture complements the existing x86/x64 kernel suite.

E12-E14 add 68 selected-byte/finite-field branch declarations; all selected forms
have PC/EAX/ESP/CF/write effects and the prefix has all-relation displacement,
register/word/CF and exact exterior-byte restoration results. The finite field
view requires complete 32-bit capacity and four-byte separation. Actual emitter
own-immediate identities, intact headers/constants and continuous live fetch
from one initialized reference image are now derived in E15-E24, including the
byte tail/alias and both continuation end PCs. General host spacing and physical
ISA/fetch remain open.
See [lean/APPENDIX_BYTE_CODE.md](lean/APPENDIX_BYTE_CODE.md).

E15-E19 now construct the reference emitter's complete live-byte predicate/patch
prefix from one initial image, entry and extent bound: actual x/y words, seven
real owners, own imm32 identities, protected constants/headers, field layout,
every fetched form/next PC and all-relation register/word/CF/exterior-byte results.
The native comparator checks 158 complete prefix packets and their exact own
operand coordinates against twelve Lean emitter exports. E20-E24 close the complete reference byte-tail/return-alias/continuation
execution and PCs. General host-spacing and physical ISA/fetch remain open. See [lean/APPENDIX_BYTE_IMAGE.md](lean/APPENDIX_BYTE_IMAGE.md).

E20-E24 add 56 checked declarations closing the complete reference x86 branch.
One initialized byte image supplies every actual fetch through the predicate,
stack exchange/CALL and selected five-step continuation. Its actual target and
both end PCs are derived; EAX/ESP restored, CF=false, every reached DWORD write
code-owned, all protected packets intact and every original byte outside the
three final scratch fields restored. CALL's temporary DEFSTACK address word is
included. Only initial image, entry and finite extent are execution premises.
The endpoints are finite observation boundaries, not source halt. General native
host spacing and physical ISA/fetch/other architectural state remain separate.
See [APPENDIX_BYTE_IMAGE.md](../lean/APPENDIX_BYTE_IMAGE.md).

E25-E30 add 72 checked declarations for independently spaced, ordered forward
x86 branch blocks. One original byte image supplies all pure fetches; the actual
Taken-Fall displacement, both continuation end PCs, EAX/ESP/CF restoration,
every owned DWORD write and exact host-gap backing bytes are derived. The native
comparator now checks all 338 complete pure packets at the actual twelve COFF
layouts, including target constants, destinations/owner coordinates and end PCs.
Only absolute payloads are normalized, with separate symbol/addend/relocation
checks. The actual host gaps are 50/12/76 bytes. Other region orderings/backward
geometry and physical ISA/configuration/coherent fetch remain separate.
See [APPENDIX_BYTE_SPACING.md](../lean/APPENDIX_BYTE_SPACING.md).

The compact [publishable LaTeX errata](../lean/errata/morse-2018-errata.tex) now records the exact M01-M07
local corrections and positive proof justifications. Its location-annotated diff
is checked against fifteen published excerpts; `python validation/limited_run.py -- python validation/audit_errata.py`
checks all 41 positive proof references and the two-page PDF. These corrections
are separate from continuing full-paper and physical ISA refinement obligations.

`python validation/limited_run.py -- python validation/run_half_frame.py` reproduces the selected split-word frame
regression after the full Lean audit. x64 follows the printed two-half patterns;
x86 tests paired 32-bit primitives. Each architecture passes 17,290 cases for
MOV/XOR/AND/OR/NOT and both CF values, with source, accumulator and full exterior
code-byte checks. `half-frame.json` records proof/source/artifact provenance.

`python validation/limited_run.py -- python validation/run_multiplication.py` builds the minimally corrected literal
Listing 11 and checks 11,458 x86 cases, fourteen real operand/stack words, all
GPRs/ESP/CF, exterior code bytes and repeated-call reuse. Its report records
88 audited multiplication proofs and fresh Lean/source/artifact provenance. Complete
loop byte-fetch/physical-ISA refinement continues separately.

The multiplication comparator also checks `ExportMultiply.lean` geometry
against COFF: 382 pure code bytes, all 55 static instruction headers, exact
block/continuation positions and the conditional/backedge displacements.
Its report records the complete 88-declaration selected word/register
execution proof; live-byte/physical refinement remains separate.

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
After refreshing run_lean.py, also run `python validation/limited_run.py -- python validation/run_zero.py` before
the final aggregate evidence audit.

`run_conversion.py` validates full-width Listing 6 USEWORD copying against
53 audited positive x86/x64 current-byte declarations. Its six export/import/
code-copy layouts pass 21,792 x86 and 24,912 x64 executions, including 454/519
live words, both incoming CF values, full-width accumulator seeds, all GPRs/SP,
complete source/destination/exterior code/data frames and repeated calls.
Eighteen complete helper packets and eight original MOFFS owners per architecture
match the actual Lean encoder; absolute/RIP targets, signed relocation bounds,
complete capacities and field/helper separation are checked. The universal
selected contract and native comparison are distinct from E05 physical CPU/fetch.

The full audit now covers 2,796 declarations and 307 unique ledger IDs.
The compact M01-M09 errata is unchanged (20 exact excerpts, 53 positive correction
references, two pages). Whole-template MOVS copying/cursor restoration/copied
field relocation remains E01/P04. After each Lean refresh, run
`python validation/limited_run.py -- python validation/run_conversion.py` along with the previously listed native
suites before the final `python validation/limited_run.py -- python validation/audit_evidence.py`.

`run_transfer.py` validates the M10-corrected literal TRANSFERDATA macro against
51 audited positive copy/plan/cursor/unified-memory/codec declarations. Both
architectures pass 6,144 executions over 48 sizes and compare every macro byte,
field and body/end coordinate with Lean: x86 3,762 bytes/1,292 headers, x64
5,682 bytes/1,160 headers, 96 cursor fields each. Native tests include arbitrary
full SI/DI values, both initial CF values, all specified GPR/SP/CF effects,
complete buffers/cursors/entire code-byte frame and repeated calls. DEFDATA's
x64 prefix accumulator effect is tested explicitly. This is finite native
execution plus universal selected data/cursor contracts. The selected MOVS
body's complete current-byte/PC trace and copied-packet/internal-RIP target laws
are now checked; full macro stage composition and whole-template absolute/MOFFS
patching remain P04/E05.

The full audit has 2,847 declarations and 312 unique ledger IDs. M01-M10 now
has 28 exact excerpt edits, 59 positive correction references and a clean
visually checked two-page PDF. Run `python validation/limited_run.py -- python validation/run_transfer.py` after
each full Lean refresh, along with the prior native suites, then encoding,
errata and final evidence audits.

E78-E82 add 54 audited results in `StringForm`, `StringExecution`, `StringMoves`,
`StringMoveTrace` and `StringTemplate`. The full audit covers 2,901 declarations
and 317 unique ledger IDs. `run_transfer.py` now binds that execution-proof
group and traverses all complete macro fixtures with Lean's actual live
classifier/fetch, checking exact re-encoding of every decoded packet, body
packet counts and byte extents. The finite execution cases/bytes and the
compact two-page M01-M10 errata remain unchanged. Reproduce with the full
Lean/native suite refresh and the final encoding/errata/evidence audits above.

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
see [the branch geometry record](../lean/APPENDIX_BYTE_SPACING.md). The audit has 3,496 declarations and
370 ledger IDs. Remaining literal source/x64 placement, physical ISA/fetch and
review-package gates retain their scope; the compact errata is unchanged.

## Input-symbol fixture - 2026-10-06

Run python validation/limited_run.py -- python validation/run_input_operand.py after the full Lean audit. Fifteen
positive declarations prove M13's source/current-target/field/purity/frame
contract. Each architecture passes 6,400 corrected and 6,400 typed-original
cases, including every GPR/SP/status flag, expected x64 DWORD zero extension,
source restoration, current target symbol, endpoint, exterior bytes and reuse.
All twelve complete loaded/COFF packets and ten relocations match actual Lean.

The new checkpoint audits 3,587 declarations and 380 ledger IDs. All fourteen
native suites and encoding/errata/aggregate provenance checks pass against the
same Lean snapshot. M01-M13 have 36 exact source excerpts and 79 local positive
references in the compact two-page TeX/PDF. The selected-x86 current-byte helper
and both-mode logical DWORD contract are explicit; universal x64 DWORD byte
execution and full literal Listing 8 remain separate completion work.

## Live DWORD scalar fixture - 2026-10-06

Run python validation/limited_run.py -- python validation/run_dword_owner.py after the full Lean audit.
Seventeen positive both-mode declarations prove the printed ten-byte
DEFDATA32 self-store, initial zero, any live operand patch/current fetch,
full AX/SP/CF/whole memory, purity and reuse. Each architecture passes 6,400
cases; forty full live packets plus the zero packet (410 bytes) and the single
COFF DIR32/REL32_4 target/addend match the actual Lean exporter. Full GPR/SP/
status flags, endpoint, current scalar and every packet byte are checked.

The central audit has 3,604 declarations and 382 ledger IDs. All fifteen native
suites and encoding/errata/aggregate evidence pass against that snapshot.
M14 replaces one macro call with the existing DEFDATA32(curtinputval,0).
M01-M14 contain 37 exact excerpts and 83 local positive references in the
two-page TeX/PDF. Full literal Listing 8 composition and the universal x64
DWORD helper remain explicit remaining work.

## Both-mode DWORD execution - 2026-10-06

The input-operand runner now binds all helper packets to the actual
DwordCode/DwordLayout model, whose 77 new declarations derive universal x86/
x64 current-byte execution, four-byte effects/purity/frames, RAX zero extension
and natural-address loads above 4GiB. All nine proved-equivalent static checks
pass on the actual layouts. Each mode passes 6,400 corrected and 6,400 typed
original cases; all twelve loaded/COFF packets and ten relocations match Lean.

The current audit has 3,681 declarations and 388 ledger IDs; all fifteen native
suites and encoding/errata/aggregate checks pass. M01-M14 and all 37 paper edits
are retained. The compact two-page TeX/PDF and its 83 positive references now
select InputDword.copy_correct. Full literal Listing 8 and physical realization/
review gates remain; the universal x64 DWORD helper gap is closed.


## Verified import reduction and bounded whole-build status

The unchanged memory-update theorems, the required core omega tactic and
Function.Injective interface compile with Init alone. SmcTuring/Memory.lean
now imports Init instead of all Std. Both local proof audits and both native
bindings were refreshed after that production change: 63 cursor declarations
and 38 full-input-update declarations remain checked, with current source,
cache and artifact hashes. Across those two fragments, 819,200 native cases pass.

The current input-update native peak is 630,366,208 bytes committed and
373,358,592 bytes sampled resident; the cursor native peak is 626,995,200 /
370,941,952 bytes. The Windows allocation limit remains 1.5 GB and checks remain
serial. The launcher now preserves Unicode output and records launcher errors.

The whole-library build remains incomplete. An initial serial pass compiled
75 modules before the Mathlib TM0 adapter hit the cap. After reducing the
foundation import, a targeted adapter recheck still hit the same cap while
loading Lean/Elab/Tactic/Grind/Main.olean.private. Both failed commands are
terminal, with logs in validation/.build/full-bounded-build.log and
mathlib-adapter-bounded.log. Do not treat either as a passing whole-library
snapshot or retry without the cap. Resolve the heavy import path while
continuing the printed interpreter obligations; the full goal remains active.


## Complete rc3 artifact mapping

The Mathlib adapter import-memory failure is resolved in an isolated trial and
in the corrected production builder. The adapter's unchanged actual source
compiled with peak aggregate commit 966,103,040 bytes and sampled resident
643,039,232 bytes under the unchanged 1.5 GB cap. The setup now supplies the
complete core/package artifact map rather than falling back to loading every
private core part.

module_artifacts.py follows the import-level rules in the installed rc3
Lean/Environment.lean and Lake/Build/Module.lean, including meta and import-all
propagation. Required private imports remain included. The compiler and its
default kernel checking are unchanged; no proof statement or axiom was added.
The builder fingerprints selected artifacts and import-header sources and
guards the actual project source path. A source-variable collision found during
integration was corrected, and affected Memory/Turing/Compiler entries were
rebuilt from their actual sources.

The whole current library is rebuilding serially; do not claim a fresh global
snapshot until it and the exact central axiom inventory audit pass. run_lean.py
now invokes the bounded direct builder and complete-artifact audit workflow.
The earlier local/native snapshots need refreshing against this final pipeline
before aggregate validation. Full Listing 8 composition remains open.
