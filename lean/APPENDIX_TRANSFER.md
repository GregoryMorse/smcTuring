# Listing 5 declared cursor fields and forward template copying

M10 changes exactly six memory operands in TRANSFERDATA. The three occurrences
of [sourceinit] become [source + DATAOFFS]; the three [destinit] operands become
[dest + DATAOFFS]. DATAOFFS is IMMOFFS (six) in 32-bit mode, where source/dest
label the DEFDATA32 instruction, and zero in 64-bit mode, where those labels
name the complete MOFFS address fields. The MOVSMACRO sequence is retained.
Listing 6's example gets the already required source/destination cursor labels.
DF=0, complete separate buffers/cursor words, valid nonwrapping pointers and a
size representable by the SUB immediate are explicit initial conditions.

The first exchange loads the intended pointer and saves the original SI/DI in
the declared cursor field. MOVS advances that pointer by exactly size. The
restoring exchange returns the old SI/DI and puts pointer+size in the field;
SUB size restores the original pointer. Every full-width old index value is
allowed. Under the nonwrapping bound the final destination SUB clears CF.

`Native/StringCopy.lean` proves the exact current-memory forward-copy equation
for every finite list of element widths. `StringPlan.lean` proves the printed
bit-mask tail conditions, equality with the exact literal MOVSMACRO plan,
nonzero/legal widths, total byte count and all-input copy/source/exterior
frames. `StringCursor.lean` proves full-width modular cursor/index restoration.
`StringFields.lean` embeds the temporary saved-index words in unified byte
memory, derives the original source bytes and proves exact final memory:
only the original source snapshot is written at the destination. Source and
complete original cursor/code exterior bytes are restored.

`StringCodec.lean` derives both initializer variants, SI/DI exchange packets,
imm8/imm32 SUB selection, absolute/RIP operands and complete code/field/body/end
geometry. Its encoder is compared with every byte of the actual native macros.
`StringForm.lean` now extends the selected instruction codec/decoder with the
actual initializer, SI/DI exchanges, imm8/imm32 SUB and all legal MOVS packets.
It proves complete roundtrip and derives packet lengths from at most three
live header bytes. `StringExecution.lean` represents full SI/DI/DF alongside
PC/AX/SP/CF and unified memory; its effects use current loads and complete
stores, sign-extended SUB operands and the actual DF-dependent index direction.

`StringMoves.lean` refines the word-index execution to the snapshot-copy proof
under explicit nonwrapping bounds. `StringMoveTrace.correct` derives every
actual-PC/current-byte body fetch, exact copy, full SI/DI advances, endpoint
and preserved AX/SP/CF/DF from the initial body and static separation/capacity.
It proves the remaining opcode/operand bytes intact after each actual store;
there is no future trace or future image premise.

`StringTemplate.lean` proves exact copied subwindows and live fetch for any
legal complete copied packet. Independent source/destination bases retain
internal rel32/RIP displacement bytes and their signed-range condition, and
RIP arithmetic reaches the moved referent. External absolute targets retain
their meaning. Absolute or MOFFS fields intended to name moved referents need
explicit destination initializers; a raw copy alone does not supply those.

`validation/run_transfer.py` retains a typed literal baseline and tests the
corrected whole macro. Both native architectures pass 6,144 executions across
48 sizes, including 0..35, all tails, 127/128 and 513, unaligned buffer offsets,
arbitrary full SI/DI seeds, both incoming CF values, complete source/destination/
cursor fields, all GPRs/SP/CF, whole code-byte frame and repeated calls.
Every complete native macro is also traversed by Lean's actual live length
classifier and fetch, with exact re-encoding at each boundary.
The baseline confirms which field the printed operands read; the positive
corrected-copy tests and universal proofs establish the intended contract.

The complete corrected DEFDATA initializer prefixes are included in native
tests. In x86 they preserve EAX. In x64 the corrected DEFADDR prefix restores
its accessed memory and leaves RAX equal to the first destination word before
the copy, as its existing contract specifies. SI/DI restoration does not imply
full-macro RAX restoration. Caller/initialization DF setup is outside this macro.

M10 is published immediately with the positive proof: the exact excerpt diff
now has 28 entries and the two-page errata has 59 positive audited references.
The 54 new instruction/body/template proofs check the complete MOVS body and
copied-packet/internal-RIP target laws. The complete selected macro execution is now checked by E91-E94;
whole-template absolute/MOFFS patching remains P04; physical CPU/segment/permission/configuration/fetch remains E05/A01.
Those obligations are retained in the full goal and are not supplied as axioms.

`StringOperands.lean` checks the actual absolute/RIP index operands and complete
imm8/imm32 SUB semantics, including sign extension and the representable copy
size. `StringWindow.lean` derives complete original packet/payload windows.
`StringInit.lean` proves both DEFDATA state contracts from that original payload,
including exact full memory restoration and the actual x64 AX result.
`StringInitTrace.lean` constructs every initializer fetch, preserving its final
MOFFS packet through the temporary pointed-word write by static separation.

`StringSetup.lean` composes both initializers and cursor exchanges: exact entry
PC, intended source/destination pointers, saved full old SI/DI, original AX/SP/CF/
DF contract and only the two cursor words written. `StringSetupTrace.initialized_trace`
derives the entire prefix's actual-byte/PC trace from one initial prefix window
and static pointed-word/initializer separation/capacity. Saving SI is proved
unable to reach any later initializer or exchange packet.

`StringRestore.lean` proves both actual XCHG/SUB pairs, including complete live
fetch, modular cursor/index restoration and derived CF=false. `StringProgram.lean`
constructs the full legal initializer/index/MOVS/restoration instruction list and
proves that it encodes to every byte of the corrected macro. All native fixtures
now compare this actual program encoding and complete prefix as well as the
original codec and live decoder.

Those eight stage modules add 50 checked declarations. E91-E94 add 46 more
results, bringing the full audit to 2,997 declarations and 329 ledger IDs.
`StringMacroTrace.correct` and `run_correct` compose the entire original-image
macro's continuous live-byte trace and exact final cursor/register/memory/code
frame. `StringMacroLayout.Ready` requires entry PC, DF=0, original complete bytes,
size<2^31 and static no-wrap/separation for code and complete buffer words.
Every later load/fetch/readiness is derived; all four tail rel32 ranges follow
from emitted size and placement. `reusable` and `reentry_trace` retain the same
macro bytes and prove the next run after explicit PC reset.
Whole-template absolute/MOFFS patching remains explicit. This does not add
an erratum: M01-M10 remain 28 exact excerpt edits and 59 positive references in
the checked two-page document.

The selected native SUB/program composition results currently use the common
nonnegative immediate bound `size < 2^31`; the underlying abstract byte-copy
and width-plan theorems remain valid for every finite natural size. Every
pointer/PC uses its separate full-width no-wrap bound. These numerical bounds
are execution-model conditions, not a restriction on the conceptual unbounded
RAM result and not an additional paper erratum.

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
