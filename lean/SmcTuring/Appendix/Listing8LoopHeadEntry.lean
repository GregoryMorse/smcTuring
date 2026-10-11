module
public import SmcTuring.Appendix.Listing8LoopDirectionSelection

public section
namespace SmcTuring.Appendix.Listing8LoopHeadEntry
open Native Listing8CopyImage Listing8DirectionGeometry Listing8HeadGeometry
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopDirection.Bounds
abbrev Current:=Listing8LoopDirection.Current

theorem input_mask (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed : Nat) (field : observed∈maskFields mode (Listing8DirectionGeometry.region mode l)) :
    DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory observed=InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape) := by
  have placed : observed∈(Listing8LiteralInput.distributionLayouts mode l.input).map (fun helper => helper.destination) := by
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts]
    rw [b.direction.mask]
    cases mode
    all_goals simp only [maskFields,List.mem_cons,List.not_mem_nil,or_false] at field
    all_goals rcases field with rfl | rfl
    all_goals simp
  rcases List.mem_map.mp placed with ⟨reader,member,hit⟩
  rw [←hit]
  have preBounds:=b.input.input.prefixBounds
  exact Listing8InputMaskEffects.destination_values mode l.input v.rule v.tape old.pending v.fresh old.mask
    preBounds.resources.inputFits (Listing8InputBounds.masks mode l preBounds.fields)
    (Listing8HeadGeometry.masks_separate mode l t b.direction)
    (Listing8InputBounds.update mode l t preBounds.fields preBounds.joined preBounds.resources)
    (Listing8InputBounds.outside mode l t preBounds.fields preBounds.joined preBounds.resources) _
    (Listing8MainPrefix.entry mode l t v preBounds state entry forward current.input.prefixCurrent)
    (Listing8MainInputImage.current mode l t v old b.input.input state entry forward current.input)
    (Listing8MainPrefixFrames.head_cursor mode l t v preBounds state entry forward current.input.prefixCurrent)
    (Listing8MainPrefixSources.tape_symbol mode l t v preBounds b.input.pointersOutside state entry forward current.input.prefixCurrent) reader member

theorem mask (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed : Nat) (field : observed∈maskFields mode (Listing8DirectionGeometry.region mode l)) :
    DwordCode.get (Listing8LoopDirection.finish mode l t v state).principal.memory observed=InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape) := by
  have frame:=Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) b.direction.capacity (Listing8MainInput.finish mode l t v state)
    (Listing8MainInput.endpoint mode l t v old b.input state entry forward current.input) observed 4 (mask_helpers mode (Listing8DirectionGeometry.region mode l) observed field) (mask_packets mode (Listing8DirectionGeometry.region mode l) observed field)
  have kept:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame
  change DwordCode.get (Listing8LoopDirection.finish mode l t v state).principal.memory observed=DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory observed at kept
  rw [kept]
  exact input_mask mode l t v old b state entry forward current observed field

theorem input_cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    MixedMemory.getWord mode (Listing8MainInput.finish mode l t v state).principal.memory l.input.cursor=Arithmetic.encodeNat mode l.input.head :=
  Listing8MainInputFrames.head_cursor mode l t v old b.input state entry forward current.input

theorem cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    MixedMemory.getWord mode (Listing8LoopDirection.finish mode l t v state).principal.memory l.input.cursor=Arithmetic.encodeNat mode l.input.head := by
  have frame:=Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) b.direction.capacity (Listing8MainInput.finish mode l t v state)
    (Listing8MainInput.endpoint mode l t v old b.input state entry forward current.input) l.input.cursor mode.wordBytes
    (cursor_helpers mode (Listing8DirectionGeometry.region mode l) (tail_bounds mode l t b.direction))
    (cursor_packets mode (Listing8DirectionGeometry.region mode l) (tail_bounds mode l t b.direction))
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) frame
  change MixedMemory.getWord mode (Listing8LoopDirection.finish mode l t v state).principal.memory l.input.cursor=MixedMemory.getWord mode (Listing8MainInput.finish mode l t v state).principal.memory l.input.cursor at kept
  rw [kept]
  exact input_cursor mode l t v old b state entry forward current

end SmcTuring.Appendix.Listing8LoopHeadEntry
