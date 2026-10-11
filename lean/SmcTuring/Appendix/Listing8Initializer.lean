module
public import SmcTuring.Appendix.Listing8CopyTrace
public import SmcTuring.Native.StringRetarget
public import SmcTuring.Appendix.Listing8InputFields

public section
namespace SmcTuring.Appendix.Listing8Initializer
open Native Listing8Prototypes Listing8CopyImage

@[expose] def patched (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringRetarget.finish mode (Listing8ModeOffsets.sites mode (patchLayout mode l)) (Listing8CopyTrace.both mode l state)
@[expose] def tapeForm (mode : Mode) (l : Layout) (v : Values mode) :=
  StringDword.store mode (Relocation.memoryDisp mode ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input)) v.tape
@[expose] def finish (mode : Mode) (l : Layout) (v : Values mode) (state : StringExecution.State mode) :=
  StringDword.execute mode (tapeForm mode l v) (patched mode l state)
@[expose] def program (mode : Mode) (l : Layout) (v : Values mode) :=
  (Listing8CopyTrace.program mode l).map StringDword.Form.string ++
    StringRetarget.program mode (Listing8ModeOffsets.sites mode (patchLayout mode l)) ++ [tapeForm mode l v]

theorem patch_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (Listing8CopyTrace.both mode l (initial mode l v backing seed))
      (StringRetarget.program mode (Listing8ModeOffsets.sites mode (patchLayout mode l)))
      (patched mode l (initial mode l v backing seed)) :=
  StringRetarget.trace mode _ (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l))
    (Listing8ModeOffsets.valid mode _ (block_capacity mode l r) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
    (Listing8ModeOffsets.outside mode (patchLayout mode l)) _
    (Listing8CopyTrace.patch_entry mode l v r backing seed)
    (Listing8ModeOffsets.initial_patches mode _ l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState _
      (Listing8CopyTrace.copied_block mode l v r backing seed))

theorem patched_tape (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (patched mode l (initial mode l v backing seed)).principal.memory (nodeParams mode l).destination 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input) v.tape) :=
  (Listing8ModeOffsets.retargeted_owners mode _ l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState
    (block_capacity mode l r) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) _
    (Listing8CopyTrace.patch_entry mode l v r backing seed) (Listing8CopyTrace.copied_block mode l v r backing seed)).1

theorem patched_pc (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (patched mode l (initial mode l v backing seed)).principal.pc = Arithmetic.encodeNat mode (nodeParams mode l).destination := by
  have effect := Listing8ModeOffsets.effect mode (patchLayout mode l) (block_capacity mode l r)
    (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) _ (Listing8CopyTrace.patch_entry mode l v r backing seed)
  exact congrArg Execution.State.pc effect

theorem last_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (patched mode l (initial mode l v backing seed)) [tapeForm mode l v]
      (finish mode l v (initial mode l v backing seed)) := by
  have cap := block_capacity mode l r
  have d := destinations mode l
  have location := patched_pc mode l v r backing seed
  have fits : (nodeParams mode l).destination < 2^(8*mode.wordBytes) := by omega
  have current : ByteMemory.bytesAt (patched mode l (initial mode l v backing seed)).principal.memory
      (patched mode l (initial mode l v backing seed)).principal.pc.toNat 10 =
      DwordArithmetic.encode (.store (Relocation.memoryDisp mode ((nodeParams mode l).destination+10)
        (Listing8LiteralInput.sourceField mode l.input)) v.tape) := by
    rw [location,Arithmetic.encode_nat_toNat mode _ fits]
    exact patched_tape mode l v r backing seed
  exact .step (StringDword.store_encoding mode _ _ _ _ current) (.nil _)

/-- One decoder, one state and one initial global image execute both
TRANSFERDATA calls, all four MOVEMODEOFFS packets and the first copied tape
owner. Every readiness/image/fetch premise is derived from initialization. -/
theorem trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (initial mode l v backing seed) (program mode l v) (finish mode l v (initial mode l v backing seed)) :=
  StringDword.trace_append mode
    (StringDword.trace_append mode (StringDword.string_trace mode (Listing8CopyTrace.copies_trace mode l v r backing seed))
      (patch_trace mode l v r backing seed)) (last_trace mode l v r backing seed)

theorem principal_effect (mode : Mode) (l : Layout) (v : Values mode) (state : StringExecution.State mode) :
    (finish mode l v state).principal = Listing8ModeOffsets.tapeState mode (patchLayout mode l) v.tape
      (Listing8CopyTrace.both mode l state).principal := by
  rw [finish,tapeForm,StringDword.store_execute]
  rfl

theorem tape_operand (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (finish mode l v (initial mode l v backing seed)).principal.memory (Listing8LiteralInput.sourceField mode l.input) = v.tape := by
  have bounds := (Listing8LiteralComposition.field_bounds mode l.input).2.2
  have targetFits : Listing8LiteralInput.sourceField mode l.input < 2^(8*mode.wordBytes) := by
    have source := (Listing8LiteralInput.positions mode l.input).2.2.1
    have ending := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    have fits := r.inputFits
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at source ending <;> omega
  rw [principal_effect]
  exact Listing8ModeOffsets.tape_operand mode _ v.tape (block_capacity mode l r)
    (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) reach targetFits _
    (Listing8CopyTrace.patch_entry mode l v r backing seed)

theorem instruction_count (mode : Mode) (l : Layout) (v : Values mode) :
    (program mode l v).length = if mode = .x86 then 50 else 52 := by
  cases mode <;> simp [program,Listing8CopyTrace.program,StringProgram.forms,StringSetup.forms,StringSetup.sourceForms,
    StringInit.forms,StringMoves.forms,StringRestore.forms,StringPlan.widths,nodeParams,transitionParams,
    nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,StringRetarget.program,Listing8ModeOffsets.sites]

theorem code_geometry (mode : Mode) (l : Layout) :
    secondStart mode l = l.start+(if mode = .x86 then 71 else 114) ∧
    patchStart mode l = l.start+(if mode = .x86 then 147 else 233) ∧
    codeEnd mode l = l.start+(if mode = .x86 then 299 else 421) := by
  cases mode <;> simp [secondStart,patchStart,codeEnd,patchLayout,Listing8ModeOffsets.endPC,Listing8ModeOffsets.transitionEntry,
    Listing8ModeOffsets.nodeEntry,StringCodec.endpoint,StringCodec.bodyEnd,StringCodec.bodyStart,StringCodec.initialSize,
    StringCodec.exchangeSize,StringCodec.subSize,StringPlan.bytes,StringPlan.widths,StringPlan.opcode,
    nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,Nat.add_assoc]

theorem input_after_patches (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8InputMask.Intact mode l.input 0 force force force force (patched mode l (initial mode l v backing seed)).principal.memory := by
  have effect := Listing8ModeOffsets.effect mode (patchLayout mode l) (block_capacity mode l r)
    (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) _ (Listing8CopyTrace.patch_entry mode l v r backing seed)
  have bounds : ∀ site ∈ Listing8ModeOffsets.sites mode (patchLayout mode l),
      site.owner+6 ≤ l.input.start ∨ l.input.start+(inputBytes mode l).length ≤ site.owner+2 := by
    intro site member
    have siteBounds := Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
    have inputAfter := r.inputAfter
    change Listing8ModeOffsets.endPC mode (patchLayout mode l) ≤ l.input.start at inputAfter
    left
    omega
  change ByteMemory.bytesAt (patched mode l (initial mode l v backing seed)).principal.memory l.input.start
    (inputBytes mode l).length = inputBytes mode l
  change ByteMemory.bytesAt (Listing8ModeOffsets.finish mode (patchLayout mode l) _).memory _ _ = _
  rw [effect,DwordRetargetSequence.writes_window mode _ _ _ _ bounds]
  exact Listing8CopyTrace.input_retained mode l v r backing seed

/-- The actual fifth store produces the complete input image with the live
tape SUB operand, retaining the printed CNSTFRC32 AND initializer. -/
theorem input_after_tape (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8InputMask.Intact mode l.input 0 v.tape force force force (finish mode l v (initial mode l v backing seed)).principal.memory := by
  have source := (Listing8LiteralInput.positions mode l.input).2.2.1
  have ending := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have inputFits := r.inputFits
  have targetFits : Listing8LiteralInput.sourceField mode l.input < 2^(8*mode.wordBytes) := by
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at source ending <;> omega
  have location := patched_pc mode l v r backing seed
  have storeEffect := DwordArithmetic.located_effect mode (.store 0 v.tape) (nodeParams mode l).destination
    (Listing8LiteralInput.sourceField mode l.input) (patched mode l (initial mode l v backing seed)).principal rfl location reach targetFits
  have actual : (finish mode l v (initial mode l v backing seed)).principal.memory =
      DwordCode.put (patched mode l (initial mode l v backing seed)).principal.memory (Listing8LiteralInput.sourceField mode l.input) v.tape := by
    rw [finish,tapeForm,StringDword.store_execute]
    exact congrArg Execution.State.memory storeEffect
  rw [actual]
  exact Listing8InputFields.tape_patch mode l.input 0 force v.tape force force force _ (input_after_patches mode l v r backing seed)

end SmcTuring.Appendix.Listing8Initializer
