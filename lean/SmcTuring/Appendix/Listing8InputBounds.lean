module
public import SmcTuring.Appendix.Listing8PointerValues

public section
namespace SmcTuring.Appendix.Listing8InputBounds
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets := Listing8PointerCopies.Targets

/-- Initial label bindings and placement/reach certificates. Cursor/tape
values and future packet currentness are deliberately derived elsewhere. -/
structure Fields (mode : Mode) (l : Layout) : Prop where
  cursorLabel : l.input.cursor = StringCodec.sourceField mode l.start
  headLabel : l.input.head = l.sourceNode
  masksAfter : ∀ helper ∈ Listing8LiteralInput.distributionLayouts mode l.input,
    Listing8LiteralInput.endPC mode l.input ≤ helper.destination
  masksFit : ∀ helper ∈ Listing8LiteralInput.distributionLayouts mode l.input,
    helper.destination+4 ≤ 2^(8*mode.wordBytes)
  masksReach : ∀ helper ∈ Listing8LiteralInput.distributionLayouts mode l.input, mode = .x64 →
    Relocation.SignedDelta (DwordLayout.thirdPC mode helper) helper.destination
  masksNode : ∀ helper ∈ Listing8LiteralInput.distributionLayouts mode l.input,
    helper.destination+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ helper.destination

theorem masks (mode : Mode) (l : Layout) (fields : Fields mode l) :
    Listing8LiteralMaskTrace.Valid mode l.input :=
  ⟨fields.masksFit,fun helper member => Or.inr (fields.masksAfter helper member),fields.masksReach⟩

theorem positions (mode : Mode) (l : Layout) (t : Targets) (fields : Fields mode l)
    (joined : l.input.start = Listing8PointerCopies.endPC mode l) :
    l.input.start = l.start+(if mode = .x86 then 367 else 550) ∧
    Listing8LiteralInput.endPC mode l.input = l.start+(if mode = .x86 then 506 else 730) ∧
    l.input.cursor = l.start+(if mode = .x86 then 6 else 19) := by
  have main := (Listing8Initializer.code_geometry mode l).2.2
  have copies := (Listing8PointerCopies.sizes mode l t).2.1
  have inputEnd := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  refine ⟨?_,?_,?_⟩
  · rw [joined,copies,main];cases mode <;> rfl
  · rw [inputEnd,joined,copies,main];cases mode <;> rfl
  · rw [fields.cursorLabel];cases mode <;> rfl

theorem cursor_bounds (mode : Mode) (l : Layout) (t : Targets) (fields : Fields mode l)
    (joined : l.input.start = Listing8PointerCopies.endPC mode l) (r : Resources mode l) :
    l.start ≤ l.input.cursor ∧ l.input.cursor+mode.wordBytes ≤ codeEnd mode l ∧
    l.input.cursor+mode.wordBytes ≤ l.input.start ∧ l.input.cursor+mode.wordBytes < 2^(8*mode.wordBytes) := by
  have geometry := positions mode l t fields joined
  have main := (Listing8Initializer.code_geometry mode l).2.2
  have capacity := block_capacity mode l r
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Mode.wordBytes] at geometry main capacity ⊢ <;> omega

theorem outside (mode : Mode) (l : Layout) (t : Targets) (fields : Fields mode l)
    (joined : l.input.start = Listing8PointerCopies.endPC mode l) (r : Resources mode l) :
    Listing8LiteralComposition.DataOutside mode l.input := by
  have cursor := cursor_bounds mode l t fields joined r
  have ending : l.input.start ≤ Listing8LiteralInput.endPC mode l.input := by
    have geometry := positions mode l t fields joined
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at geometry <;> omega
  refine ⟨Or.inl cursor.2.2.1,?_,?_,?_⟩
  · rw [fields.headLabel]
    have nodeLarge : 10 ≤ nodeSpan mode := by cases mode <;> decide
    rcases r.nodeOutside with early | late
    · left;omega
    · exact Or.inr (by omega)
  · intro helper member
    right
    have later := fields.masksAfter helper member;omega
  · rw [fields.headLabel]
    exact fields.masksNode

/-- Both cursor RIP reaches are fixed offsets in the actual global prefix,
so no caller-supplied future cursor validity or reach is needed. -/
theorem update (mode : Mode) (l : Layout) (t : Targets) (fields : Fields mode l)
    (joined : l.input.start = Listing8PointerCopies.endPC mode l) (r : Resources mode l) :
    InputUpdate.Valid mode (Listing8LiteralInput.updateLayout mode l.input) := by
  have data := outside mode l t fields joined r
  have cursor := cursor_bounds mode l t fields joined r
  have nodeFits := (Listing8CopiedOwners.source_limits mode l r).1
  have nodeLarge : 10 ≤ nodeSpan mode := by cases mode <;> decide
  have geometry := positions mode l t fields joined
  have inputPositions := Listing8LiteralInput.positions mode l.input
  have tailEnd : CursorLayout.endPC mode (InputUpdate.body (Listing8LiteralInput.updateLayout mode l.input)) =
      Listing8LiteralInput.endPC mode l.input := InputUpdate.endpoint mode _
  have before : l.input.start ≤ (Listing8LiteralInput.updateLayout mode l.input).start := by
    have point := inputPositions.2.2.2.2.1
    change (Listing8LiteralInput.updateLayout mode l.input).start = l.input.start+(if mode = .x86 then 100 else 139) at point
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at point <;> omega
  have bodyStart : (Listing8LiteralInput.updateLayout mode l.input).start ≤
      (InputUpdate.body (Listing8LiteralInput.updateLayout mode l.input)).start := by
    simp only [InputUpdate.body];omega
  have cursorOutside : l.input.cursor+mode.wordBytes ≤ (Listing8LiteralInput.updateLayout mode l.input).start := by omega
  have tapeOutside : l.input.head+10 ≤ (Listing8LiteralInput.updateLayout mode l.input).start ∨
      CursorLayout.endPC mode (InputUpdate.body (Listing8LiteralInput.updateLayout mode l.input)) ≤ l.input.head+6 := by
    rw [tailEnd]
    rcases data.tape with early | late
    · left;omega
    · exact Or.inr late
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,Or.inl cursorOutside,tapeOutside⟩
  · rw [tailEnd];exact r.inputFits
  · exact Nat.le_of_lt cursor.2.2.2
  · change l.input.head+10 ≤ _
    rw [fields.headLabel];omega
  · change l.input.cursor+mode.wordBytes ≤ l.input.head+6 ∨ l.input.head+10 ≤ l.input.cursor
    rw [fields.headLabel]
    have whole := code_to_input mode l r
    rcases r.nodeOutside with early | late
    · right;omega
    · left;omega
  · left;change l.input.cursor+mode.wordBytes ≤ _;omega
  · exact tapeOutside.elim (fun early => Or.inl (Nat.le_trans early bodyStart)) Or.inr
  · intro wide;subst mode
    simp only [reduceCtorEq,ite_false] at geometry inputPositions
    unfold CursorLayout.middlePC CursorLayout.exchangeSize InputUpdate.body Listing8LiteralInput.updateLayout
    rw [inputPositions.2.2.2.2.1,geometry.1,geometry.2.2]
    simp [Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix]
    unfold Relocation.SignedDelta Relocation.delta
    omega
  · intro wide;subst mode
    change Relocation.SignedDelta (CursorLayout.endPC .x64 (InputUpdate.body (Listing8LiteralInput.updateLayout .x64 l.input))) l.input.cursor
    rw [tailEnd]
    simp only [reduceCtorEq,ite_false] at geometry
    rw [geometry.2.1,geometry.2.2]
    unfold Relocation.SignedDelta Relocation.delta
    omega

end SmcTuring.Appendix.Listing8InputBounds
