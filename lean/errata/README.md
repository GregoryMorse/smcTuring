# Minimal publishable errata

Current inventory: **M01-M20, 60 exact excerpts, 128 positive references, two pages**; fresh complete proof binding passes. Earlier dated counts/hashes below are historical; the current audit is recorded at the end.

[morse-2018-errata.tex](morse-2018-errata.tex) is a standalone two-page errata:
one page of local corrections and one page of positive justification. It uses
the published article's page numbers, including the dissertation's reproduced
article wherever those original page/listing labels are retained.

[morse-2018-minimal.diff](morse-2018-minimal.diff) gives the exact substitutions
and insertions. It is a location-annotated excerpt diff, with PDF line wrapping
and ligatures normalized. The publisher's original LaTeX source is unavailable
in this repository, so this is a text correction specification rather than an
apply-ready patch to that source. [edits.json](edits.json) records all sixty
edits and the exact SHA256 of the source PDF.

The code changes are one DEFADDR mnemonic, one independent branch parameter,
one target-operand substitution, three identifier spellings, Listing 11's operand offset, displacement sign and two continuation labels, and Listing 6's trailing-zero description and two +1 shift gaps. Other entries
state the storage/continuation preconditions and clarify the existing abstract
unbounded model, reached-instruction purity and split-word interpretation.
M09 makes DEFZERO's DWORD type explicit and replaces zero by the existing
CNSTFRC32 to force its complete immediate; one XOR still clears the live word.
M01 retains the original macro's exact final accumulator and memory effect.
M05 retains the existing comparison/stack/continuation algorithm. The normal
MASM NEAR-code-label CALL typing is retained. M06 binds the already declared
comparison-mask argument and Table II's already defined IMMOFFS constant;
correcting these names does not change the resolved instruction operation.
M07 retains the shift-and-add algorithm; checked block/product contracts and
11,458 full native x86 cases validate the four local substitutions.

M08 retains the constant emitter: all-input arithmetic/compiled-word trace, signed
low products, zero, legal shifts, accumulator/purity/frame, the complete
original-image live-byte/emitter-layout contract and reuse, and 54,366 native
x86 runs plus 11,350 complete pure packets justify its three local substitutions.

The positive proof references are checked against the pinned full Lean axiom
audit. This document records the verified local corrections. It does not
certify the entire literal Listing 8, every supplementary arithmetic listing,
native half-field placement, or physical CPU fetch coherence; those remain
in the [completion audit](../COMPLETION_AUDIT.md). Dolan source normalizations
belong to that separate foundation and are absent from this article's errata.
The variable-length-address sentence specifies a possible idealized
representation; the checked universality theorem uses abstract unbounded word
operands, not a new x86 byte encoding for arbitrary addresses.

Reproduce from the repository root (MiKTeX and PyMuPDF are installed here):

```powershell
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape -output-directory=output/pdf lean/errata/morse-2018-errata.tex
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape -output-directory=output/pdf lean/errata/morse-2018-errata.tex
python validation/audit_errata.py --write-diff
python validation/audit_evidence.py
```

Run the full Lean/native refresh first if proof or implementation source changes.
The current audit checks 45 original excerpts against the cached publication,
regenerates/checks the exact minimal diff, verifies 111 positive proof
references and their permitted axioms, checks the repaired native primitive,
and verifies the two-page PDF's text and compile log. Visual PDF inspection is
also required after a document edit. No journal submission has been made.

M10 substitutes the declared cursor-field operand in six positions and makes
Listing 6's example cursor labels explicit. DATAOFFS is IMMOFFS for the printed
32-bit DEFDATA owner and zero for its 64-bit MOFFS field label. DF=0, complete
separate buffers/cursor words and representable pointers/SUB size are explicit.
Positive byte-copy/cursor/memory-restoration proofs and 6,144 executions per
architecture validate the intended copy and original SI/DI/cursor restoration.
The exact diff now has 35 excerpt entries and the errata has 74 audited positive
correction references; whole-template relocation/live-fetch work continues.

M11 retains Listing 12's algorithm and instruction order with four verified
local substitutions: copy the divisor into lbl13, use target-minus-next exit
delta, rename the existing body continuation, and reset the CALL field at OPSZ1.
M06 already corrects the counter spelling. The printed signed-prefix scope and
wrapped hexadecimal operand are correct.

The correction now has a complete positive original-image current-byte proof
in `DivisionByteCorrect.correct` and `reusable_correct`, covering all four modes,
all nonzero inputs, signed integer contracts, exact CF/registers/PC/reset,
code-write purity and original-byte restoration outside scratch/result fields.
The corrected native fixture passes 52,648 executions with independent integer
oracle and register/input/code-frame/reuse checks. All 344 packets, 2,532 bytes,
333 DIR32 sites and 91 mode-owned fields match the actual Lean image.

The terminal checkpoint has 3,523 declarations and 373 ledger IDs. E04 is checked for the
selected finite x86 byte machine; full physical ISA/configuration/fetch remains
E05/A01. M12 additionally corrects the reusable terminal marker; M01-M12 contain 35
exact excerpts and 74 positive errata references in the compact two-page TeX/PDF. [POLICY.md](POLICY.md) records the author's minimum-change,
positive-proof and immediate-clearance policy.


M12 makes the DWORD terminal store target its own immediate at IMMOFFS and
states the observation boundary in one sentence. Both-mode current-byte
correctness, AX/SP/CF and whole-memory/output preservation, code-owned writing
and reusable encoding are checked. Each architecture passes 4,128 corrected and
4,128 typed-original native cases; exact loaded and COFF packets match Lean,
including x64 REL32_4. See [the positive terminal contract](../APPENDIX_TERMINAL.md).


The later accumulator/finalization checkpoint audits 3,572 declarations and
378 ledger IDs. E139-E143 prove the unchanged four-instruction full-width
Listing 9 sequence, original pointer initialization, actual body/epilogue/terminal
composition, purity, live reuse and output preservation. Each architecture
passes 38,400 cases with complete loaded/object packet comparison. No additional
paper edit was established, so M01-M12, 35 excerpts, 74 local positive references
and the two-page publishable TeX/PDF are retained. The body contract remains to
be discharged for literal Listing 8; optimized/x64 field placement and physical
realization retain their scope.

## Input-symbol operand checkpoint - 2026-10-06

M13 adds only + IMMOFFS to the source of Listing 8's inputupdate USEWORD32
call. The label names COMPARE32's first instruction; the intended symbol is
its live DWORD immediate at offset six. The same three instructions now copy
that symbol to the XOR immediate at offset three. Fifteen positive declarations
prove source restoration, derived current target code, selected-x86 live trace,
AX/SP/CF, purity and source/header/exterior frames; the logical DWORD contract
holds in either mode. Both native architectures pass 6,400 corrected and 6,400
typed-original cases, with complete loaded/COFF packet comparison.

M01-M13 now comprise **36 exact excerpts and 79 local positive proof references**.
The publishable TeX/PDF remains two pages and includes this local edit immediately
after its proof and native checks. The full checkpoint has 3,587 audited
declarations and 380 ledger IDs. Full Listing 8 and universal long-mode DWORD
byte execution remain explicit. See [the positive input-operand
contract](../APPENDIX_INPUT_OPERAND.md).

## DWORD scalar-owner checkpoint - 2026-10-06

M14 replaces only DEFDATA(0, curtinputval) by the existing
DEFDATA32(curtinputval, 0). The label/value order and complete DWORD at offset
six match both consumers. Seventeen positive both-mode current-byte results
derive zero initialization, a complete packet after any live operand patch,
preservation of that live symbol/full AX/SP/CF/whole memory, purity and reuse.
Each architecture passes 6,400 cases; forty live packets plus the zero packet
and the complete COFF relocation match actual Lean. See
[the scalar-owner contract](../APPENDIX_DWORD_OWNER.md).

M01-M14 now comprise **37 exact excerpts and 83 positive local proof references**.
The immediately updated publishable TeX/PDF remains two pages. Full literal
Listing 8 composition and the remaining architecture/review gates continue;
this local declaration is proved without introducing a new primitive.

## Stronger M13 evidence - 2026-10-06

The paper edits and 37 exact excerpts are unchanged. E148-E153 now give 77
additional universal both-mode DWORD codec/layout/effect/live-image/input-copy
proofs. The native comparator uses that actual encoder, checks nine proved
static premises and covers real x64 addresses above 4GiB. The 83 positive
errata references now select InputDword's both-mode correction, purity/current
source/source-header results. The two-page TeX/PDF cites
InputDword.copy_correct. No new paper erratum is introduced. See
[the positive DWORD helper contract](../APPENDIX_DWORD_COPY.md).


## M15 and remote artifact replay (2026-10-06)

M15 changes only the last two arguments of the two Listing 8 mask-copy calls:
`inputvalmask, IMMOFFS` becomes `inputvalmask + IMMOFFS, 0`. The current
inventory is 39 exact source excerpts and 91 positive correction references;
earlier M01-M14 counts above are historical. Listing8MaskCopy supplies the
positive both-mode mask-immediate copy and six-step x64 broadcast contracts.
The full literal trace must still insert both calls between NOT and update.

The PDF was rebuilt and visually checked at two pages in the remote scope.
The task-local Tectonic 0.17.0 musl archive was downloaded from the official
release, SHA-256
8533d07f9ccbd7a65824b9e0459041bca34af1eb33daba48f59215593753a3b7.
No shared package installation or external publication occurred. Rebuild with
that compiler's `--untrusted --only-cached --keep-logs --keep-intermediates`
options, output directory `output/pdf`, and the task-local cache. The standard
Windows pdflatex replay above remains valid. After a passing complete Linux
build, `python3 validation/audit_errata.py --remote-source-proof` checks all
original excerpts, the deterministic diff, current audited proof references
and PDF text/log. Its explicitly scoped report is
`validation/remote-evidence/errata-source-proof.json`; it does not replace the
fresh Windows/native aggregate gate.


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


## M16/M17 prototype-copy corrections (2026-10-06)

The current M01-M17 inventory has **45 exact original excerpts and 111 positive
proof references**. Earlier counts and evidence below/above are historical.
M16 gives DEFINPUT the generalized node's back/forward owners, initializes their
values to adjacent node entries and changes the first copy extent to the full
node's entry-to-end distance. M17 inserts transition entry/end labels and changes
only the second TRANSFERDATA's destination and size to those boundaries.
DEFADDR's label is its final MOFFS operand, so it cannot name a whole-copy entry.
`Listing8Prototypes` proves all complete fields and selected encoder lengths;
`Listing8PrototypeCopy` proves actual literal full-copy traces/values, preserved
zero neighbors after a ten-byte copy, and opcode corruption when the transition
copy targets its operand label. No optional assembler MOV size is assumed by
the entry-to-end repairs.

M01's supporting precondition now permits any complete code-contained word.
Temporary opcode/address writes must be restored before affected fetches.
Its mnemonic repair and exact published anchor are unchanged; the existing
DEFADDR purity/current-fetch and StringInitTrace proofs justify the broader
storage placement needed by the actual TRANSFERDATA initialization.

The actual printed source binding is tape symbol to SUB immediate, rule symbol
to M14 scalar. `Listing8SourceEffects` positively proves that input trace/effect;
the earlier candidate-equals-tape specialization remains valid and unchanged.
No source edit is claimed for this proof-variable binding correction.

The updated compact TeX/PDF was compiled with task-local Tectonic using only
cached resources and no shell escape, then both final pages were rendered and
viewed. `validation/remote-evidence/errata-build.json` records exact artifact
hashes. Linux source/proof evidence and the fresh Windows/native aggregate
remain distinct. This milestone does not finish the whole interpreter.


## M18/M19 cursor and pending-pointer repairs (2026-10-06)

The current inventory is M01-M19: **55 exact source excerpts and 121 positive
references**. Earlier snapshots above are historical. M18 applies the existing
M10 DATAOFFS to Listing 8's DEFDATA cursor operands: curitapeinit, curttapeinit,
itapeptr and ttapeptrinit. The exact diff records eight original excerpts,
including the two separately identified input exchanges. This selects the
value at MOV-entry+6 on x86 and at the MOFFS operand label on x64.
Listing8CursorFields proves both incorrect-field counterexamples, the exact
field identity and the actual restored source cursor after both copies.

M19 changes only the pending transition pointer's copy destination/stride/source
and its update destination/stride. The copy targets ttapeupdate+IMMOFFS with
OPDBLARGSZ packet spacing, reads curttapeinit+DATAOFFS with PTRSZ32 spacing, and
the XOR update targets that cursor with PTRSZ32 spacing. The imm32 fields are
at +6/+16 in two ten-byte packets; pointer halves are four bytes apart.
Listing8PointerTargets proves opcode corruption at the printed copy target,
header-preserving immediate replacement, exact located pointer-half XOR effects
and old/new selection. Existing HalfWords split_xor and repeated_masks justify
the corresponding whole pointer algebra. The complete later control trace is
still an open composition obligation.

The compact PDF uses two columns on each of its two pages to retain every
correction and positive justification. The original M04 full-RAX condition is
retained. These repairs and their targeted positive proofs do not assert
native MASM acceptance, physical fetch coherence or full interpreter completion.
The Windows aggregate validator now expects 55 excerpts and 121 references;
its actual bounded run and new PDF QA remain the coordinator's separate gate.


### Fresh complete proof/source/PDF audit for M01-M19

The serial exact-rc3 Linux build exited 0: 390 modules, 4,213 declarations,
419 source/helper hashes; source-matched audit gate passed. Proof/helper inputs
were fixed during the complete audit. Lean report SHA-256: `ee06c0d29ea6602487c73e0eb255ca0344b39700a646eb9f0f4a42b4b12b9a1b`.
Axiom log SHA-256: `5f4b9b314f9e1b399b44029e82af19358cdeda7d5c554f4d1768972602dda427`. Only the standard three allowed axioms occur.
The separate source/proof/PDF gate passes all 55 excerpts, 121 positive refs
and two pages; report SHA-256: `6a987f1f5db62759b66c252d3ae8082517f67e9b152012d7ad39484f4e707590`.
TeX SHA-256: `588203bf3ece866dd03ce85f418b8eda512ffbd9a520cf7e9cdde3eb3944f7ad`; PDF SHA-256: `79ea4d705a20ce6ccea9821b4629d69fffa446e18f3f4d98b479fcfe71914df9`.
The build/visual metadata is validation/remote-evidence/errata-build.json.
No Windows/native aggregate, complete interpreter or physical ISA proof is
claimed by this checkpoint. Earlier counts/hashes above are historical.


### Current copied-owner audit refresh (2026-10-06)

The unchanged M01-M19 source/diff/TeX/PDF passes the fresh source/proof gate
against 395 modules, 4,278 declarations and 424 source/helper hashes.
Lean report SHA-256: `9966cab3e1cae69b29346ccbc29b42232dc4f675794127341263963bb14590bc`; axiom log SHA-256: `3117a24c43feabd48354c10e1a110e9b3bb74a90e8965581c4d248d8587eccda`.
Errata source/proof report SHA-256: `c6c543707ce5e48bf1c25da18c7fd42726a5256780cccab37c563f7474b8119c`.
The earlier complete report is historical; the same 55 anchors/121 refs/two-page
PDF are current. The five new Listing8CopiedPointer/OwnerSequence/OwnerImage/
CopiedOwners/OwnerInput modules prove the actual 69/71-step original-source-
addressed owner prefix and derived input/cursor/tape fields. No new paper edit,
Windows/native aggregate or complete interpreter is claimed.


### Fresh source/proof/PDF binding after direction-value proofs

The current complete source-matched Linux audit passes 427 production modules
and 4,472 declarations. M01-M19 remains 55 exact excerpts, 121 positive proof
references and two pages. No erratum, TeX or PDF content changed this turn.
Lean report SHA-256: `f0318ddabe05fc163cf8402190b3398159ec08ea6e0d819ce7aa4b2cc3ca364c`.
Errata report SHA-256: `904ef7dfbda8fbcf5866c3268ab04d63c748a817d98d90ec499694f19fe4a858`.
TeX SHA-256: `588203bf3ece866dd03ce85f418b8eda512ffbd9a520cf7e9cdde3eb3944f7ad`. PDF SHA-256: `79ea4d705a20ce6ccea9821b4629d69fffa446e18f3f4d98b479fcfe71914df9`.
Coordinator M04 two-page local QA is acknowledged. Expanded local PDF QA and
fresh Windows/native aggregation remain separate gates. Earlier hashes above
are historical.


### Fresh source/proof/PDF binding after actual head-update composition

The current complete source-matched Linux audit passes 436 production modules
and 4,537 declarations. M01-M19 remains 55 exact excerpts, 121 positive proof
references and two pages. No erratum, TeX or PDF content changed this turn.
The original failure-CALL expression is positively proved: fail=CALL+5 makes
the printed subtraction the original backedge displacement; masked XOR selects
failure and the printed store restores the backedge. Global stack/control remains open.
Lean report SHA-256: `899e80e845d5080cd795375bb0b8a541c73c2c8b0a1706714f0746c28d7cf530`.
Errata report SHA-256: `67728eeaa39208396b1a47bc8bc19de9dde962aa73d1840c79ce4c8ef3ebbb7b`.
TeX SHA-256: `588203bf3ece866dd03ce85f418b8eda512ffbd9a520cf7e9cdde3eb3944f7ad`. PDF SHA-256: `79ea4d705a20ce6ccea9821b4629d69fffa446e18f3f4d98b479fcfe71914df9`.
Coordinator M04 two-page local QA is acknowledged. Expanded local PDF QA and
fresh Windows/native aggregation remain separate gates. Earlier hashes above
are historical.


### Fresh source/proof/PDF binding after actual state-update composition

The complete source-matched Linux audit passes 447 production modules and 4,603
declarations. M01-M19 remains 55 exact excerpts, 121 positive references and
two pages. No erratum, TeX or PDF content changed this turn. The actual printed
M19 pending-pointer copy/XOR/mask/state update is composed from the original
initialized image; its conditional next/newState cursor and retained head/tape
values are proved. Global failure/stack/control remains open.
Lean report SHA-256: `651264f77d4a98e66ee9f3621d7c9b2b8827407287fa65a6c2f1d8b9cd5e4b51`.
Errata report SHA-256: `510c9f2e5c19068bb03c76c698ebd2db171be9e65c4b9e8f3d52b0c682befc9b`.
TeX SHA-256: `588203bf3ece866dd03ce85f418b8eda512ffbd9a520cf7e9cdde3eb3944f7ad`. PDF SHA-256: `79ea4d705a20ce6ccea9821b4629d69fffa446e18f3f4d98b479fcfe71914df9`.
Coordinator M04 two-page local QA is acknowledged. Expanded local PDF QA and
fresh Windows/native aggregation remain separate gates. Earlier hashes above
are historical.


### Fresh source/proof/PDF binding after actual failure-mask composition

The complete source-matched Linux audit passes 465 production modules and 4,715
declarations. M01-M19 remains 55 exact excerpts, 121 positive references and
two pages. No erratum, TeX or PDF content changed this turn. The actual full
pointer comparison and fail-mask/CALL-operand selection are composed from one
initialized image; full transition/head/tape values remain proved. Actual
stack/CALL/continuations/reset and loop/interpreter/output remain open.
Lean report SHA-256: `9b14ad83ab36be4b7c7f6cb8363e8d3b0a3201e1c57774c2ca6753bfe6fbcd3b`.
Errata report SHA-256: `e88d801878df3f7469b6586f70a98b5c736ff3b804b1d3172e034baea6380b5b`.
TeX SHA-256: `588203bf3ece866dd03ce85f418b8eda512ffbd9a520cf7e9cdde3eb3944f7ad`. PDF SHA-256: `79ea4d705a20ce6ccea9821b4629d69fffa446e18f3f4d98b479fcfe71914df9`.
Coordinator M04 two-page local QA is acknowledged. Expanded local PDF QA and
fresh Windows/native aggregation remain separate gates. Earlier hashes above
are historical.


## M20 accumulator-storage operand repair

The original PDF pages 124 and 127 were rendered and visually checked. Listing 2 places an x86 DEFDATA32 label at the MOV header, while its x64 MOFFSMOV label denotes the operand. Listing 9 uses bare labels at four memory operands and in the pointer's initial value. M20 applies the already defined DATAOFFS at those five exact occurrences. Instruction order, the save declaration and the algorithm are retained. Listing9Fields proves the operand locations and corrected decoded pointer; Listing9PackedLayout derives the static bounds, and Listing9ExecutionImage.execute derives every packet contract from the emitted bytes and executes the actual entry/body/epilogue. Full seed AX restoration is stated at the epilogue boundary, before trailing storage; fallthrough, physical exit and global ownership remain separate unfinished gates.

The new seven positive references bring the exact source/proof inventory to 60 excerpts and 128 references. The errata audit helper changes only these counts/markers and positive references. The new TeX/PDF compiled with cached task-local Tectonic and both final pages were rendered and visually checked without clipping or overlap. The complete current kernel/axiom binding passes. Prior dated counts and hashes are historical.


### Fresh M01-M20 proof/source/PDF binding

The complete serial Linux audit passes 732 production modules, 6,072 declarations and 761 source/helper hashes. All 60 exact excerpts, 128 positive references and two PDF pages pass the source/proof/PDF gate. Lean report SHA-256: `061875145a2e73dfa919af94b3490beef8325495e51d9f0f895d56a640753547`. Errata report SHA-256: `b7e58efdd65856781a6ce799f042f2ef68da861c920a1b8d01ebe2726f83a9ae`. TeX SHA-256: `2beef69ea3543e38a3888c6c8d53b6401623cf47343c94c6a3730a34d3f9e85a`; PDF SHA-256: `9dc820126a93b9f93c91053ec9cca991670c2ec0b6bef04166f7be73c7e59c57`. All proof/helper/errata inputs stayed fixed during the audit. Native Windows aggregation, trailing-storage/physical exit, global purity and every full-paper gate remain required. Earlier dated hashes/counts are historical.


### Fresh complete Listing 9 fallthrough/code-write audit binding

The unchanged M01-M20 / 60 excerpts / 128 positive references / two-page TeX/PDF passes the fresh source/proof/PDF gate against 741 production modules, 6,107 declarations and 770 source/helper hashes. Lean report SHA-256 `240348153649157909041b657887dd5c686c7ae9b8e88826171b9d657fd1ef20`; errata report SHA-256 `438bb62680c2f8364215f0c3ae6e8ac58bca372e0a9b5ad77b6cc29e8a025868`. TeX SHA-256 `2beef69ea3543e38a3888c6c8d53b6401623cf47343c94c6a3730a34d3f9e85a`; PDF SHA-256 `9dc820126a93b9f93c91053ec9cca991670c2ec0b6bef04166f7be73c7e59c57`. Only this fresh binding documentation changes after audit exit.

The full emitted native trace now includes both trailing declarations. Full seed AX is restored at the intermediate epilogue boundary, as M20's existing justification states. Through full fallthrough x86 retains seed AX; x64 loads the nonzero save-field address, retaining seed RAX exactly when they match. Positive complete code-word writes cover entry/exit and both declarations. No additional paper edit is established. Whole actual Listing 8 body purity, TM compilation including empty rules, precise physical ISA/fetch/ABI/stop and fresh bounded Windows aggregation remain required. Earlier audit hashes/counts are historical.


### Fresh ordered copy-prefix complete audit binding

Unchanged M01-M20 / 60 excerpts / 128 positive references / two-page TeX/PDF passes the source/proof/PDF gate against the fresh complete audit of 749 production modules, 6,131 declarations and 778 source/helper hashes. Lean report SHA-256 `5bf25964fdeca10b48a98b5027d955c08d9c885e5789691c03dd5a3b44393f37`; errata report SHA-256 `0209cbdbdec67706ef3e33ecebb2dec412538af4a4763666990780d4a43b9d09`. TeX SHA-256 `2beef69ea3543e38a3888c6c8d53b6401623cf47343c94c6a3730a34d3f9e85a`; PDF SHA-256 `9dc820126a93b9f93c91053ec9cca991670c2ec0b6bef04166f7be73c7e59c57`. Only this binding documentation changes after terminal audit exit. No new erratum is established. Whole actual Listing 8 ownership/composition, logical TM graph compilation, physical native bindings and fresh bounded Windows aggregation remain open. Coordinator M04 local two-page rebuild and visual QA is acknowledged. Earlier hashes/counts are historical.


### Fresh actual graph prefix complete audit binding

Unchanged M01-M20 / 60 excerpts / 128 positive references / two-page TeX/PDF passes the source/proof/PDF gate against the fresh complete audit of 764 production modules, 6,183 declarations and 793 source/helper hashes. Lean report SHA-256 `cd95dab08acbe4911f7aaa4410400b43087cf0ab8622dff4c7e7b88d541e4583`; errata report SHA-256 `d150cc7612a48efd70e6b817f20d4758b6741e9789bf35217289a3f309088da9`. TeX SHA-256 `2beef69ea3543e38a3888c6c8d53b6401623cf47343c94c6a3730a34d3f9e85a`; PDF SHA-256 `9dc820126a93b9f93c91053ec9cca991670c2ec0b6bef04166f7be73c7e59c57`. Only this binding documentation changes after terminal audit exit. No new erratum is established. Whole actual Listing 8 ownership/composition, logical TM graph compilation, physical native bindings and fresh bounded Windows aggregation remain open. Coordinator M04 local two-page rebuild and visual QA is acknowledged. Earlier hashes/counts are historical.
