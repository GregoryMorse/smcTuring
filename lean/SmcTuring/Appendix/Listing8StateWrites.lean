module
public import SmcTuring.Appendix.Listing8StateTrace
public import SmcTuring.Native.StringDwordRuns
public import SmcTuring.Native.DwordPacketWrites

public section
namespace SmcTuring.Appendix.Listing8StateWrites
open Native Listing8StateLayout Listing8StateBounds

theorem helper_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd)
    (cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd) :
    ∀ helper∈helpers mode layout,(codeStart≤helper.source ∧ helper.source+4≤codeEnd) ∧
      (codeStart≤helper.destination ∧ helper.destination+4≤codeEnd) := by
  intro helper member
  cases mode
  all_goals simp only [helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [endPC,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes]
    at inside cursor ⊢;omega

theorem packet_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd)
    (cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd) :
    ∀ site∈packets mode layout,codeStart≤site.target ∧ site.target+4≤codeEnd := by
  intro site member
  cases mode
  all_goals simp only [packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [endPC,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes]
    at inside cursor ⊢;omega

/-- Both pending-pointer halves and every live XOR/AND/update packet write
complete fields in code, with future native PCs derived from execution. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (bounds : Bounds mode layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd)
    (cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8StateTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have first:=StringSequenceWrites.owned mode codeStart codeEnd (helpers mode layout) layout.start (helper_chain mode layout)
    (helper_valid mode layout bounds) (helper_fields mode codeStart codeEnd layout inside cursor) state entry
  have last:=DwordPacketWrites.owned mode codeStart codeEnd (packets mode layout) (newPC mode layout) (packet_chain mode layout)
    (packet_valid mode layout bounds) (packet_fields mode codeStart codeEnd layout inside cursor)
    (Listing8StateTrace.helperFinish mode layout state) (Listing8StateTrace.helper_endpoint mode layout bounds state entry)
  rw [Listing8StateTrace.program,List.map_append,StringWrites.owned_run_append,StringDwordRuns.run]
  exact ⟨first,last⟩

end SmcTuring.Appendix.Listing8StateWrites
