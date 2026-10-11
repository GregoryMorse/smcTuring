module
public import SmcTuring.Appendix.Listing8HeadTailTrace
public import SmcTuring.Native.DwordXorWrites
public import SmcTuring.Native.DwordPacketWrites

public section
namespace SmcTuring.Appendix.Listing8HeadTailWrites
open Native Listing8DirectionLayout Listing8HeadTailBounds

theorem xor_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd)
    (cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd) :
    ∀ helper∈xorLayouts mode layout,(codeStart≤helper.source ∧ helper.source+4≤codeEnd) ∧
      (codeStart≤helper.destination ∧ helper.destination+4≤codeEnd) := by
  intro helper member
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at inside cursor ⊢;omega

theorem packet_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd)
    (cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd) :
    ∀ site∈masks mode layout++heads mode layout,codeStart≤site.target ∧ site.target+4≤codeEnd := by
  intro site member
  cases mode
  all_goals simp only [masks,heads,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at inside cursor ⊢;omega

/-- Difference helpers, mask packets and both pointer halves all write
complete fields in code. No future cursor value or native PC is a premise. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (bounds : Bounds mode layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd)
    (cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (selectionEnd mode layout)) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8HeadTailTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have first:=DwordXorWrites.sequence_owned mode codeStart codeEnd (xorLayouts mode layout) (selectionEnd mode layout) (xor_chain mode layout)
    (xor_valid mode layout bounds) (xor_fields mode codeStart codeEnd layout inside cursor) state entry
  have fields:=packet_fields mode codeStart codeEnd layout inside cursor
  have middle:=DwordPacketWrites.owned mode codeStart codeEnd (masks mode layout) (maskPC mode layout) (masks_chain mode layout)
    (fun site member => packets_valid mode layout bounds site (List.mem_append_left _ member))
    (fun site member => fields site (List.mem_append_left _ member))
    (Listing8HeadTailTrace.xorFinish mode layout state) (Listing8HeadTailTrace.xor_endpoint mode layout bounds state entry)
  have last:=DwordPacketWrites.owned mode codeStart codeEnd (heads mode layout) (directionPC mode layout) (heads_chain mode layout)
    (fun site member => packets_valid mode layout bounds site (List.mem_append_right _ member))
    (fun site member => fields site (List.mem_append_right _ member))
    (Listing8HeadTailTrace.maskFinish mode layout state) (Listing8HeadTailTrace.mask_endpoint mode layout bounds state entry)
  rw [Listing8HeadTailTrace.program,List.map_append,List.map_append,StringWrites.owned_run_append,
    StringWrites.owned_run_append,StringWrites.run_append,DwordXorWrites.sequence_run]
  unfold Listing8HeadTailTrace.xorFinish
  rw [DwordPacketWrites.run]
  simpa only [Listing8HeadTailTrace.maskFinish,Listing8HeadTailTrace.xorFinish] using And.intro (And.intro first middle) last

end SmcTuring.Appendix.Listing8HeadTailWrites
