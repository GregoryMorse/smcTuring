module
public import SmcTuring.Appendix.Listing8GlobalControlTemplates
public import SmcTuring.Appendix.Listing8ResetTemplateBindings
public import SmcTuring.Native.JointTemplateStates

public section
namespace SmcTuring.Appendix.Listing8GlobalControlRegions
open Native Listing8GlobalControlLayout

theorem jump (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Listing8JumpReturn.Current mode origin failed state.principal.memory) :
    StringStoreRegions.Run mode (Allowed mode origin) (Listing8JumpReturn.program mode origin failed) state :=
  BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) (Allowed mode origin) _ state
    (fun _ _ slots => Or.inl slots) (Listing8JumpSlotRegions.complete mode origin failed state entry capacity current)

/-- All seven exact reset fields protect both target regions and the CALL
opcode. The displacement itself is allowed to change to its restored value. -/
theorem reset_fields (mode : Mode) (origin transitions address count : Nat)
    (allowed : Listing8ResetStoreRegions.Allowed mode (Listing8GraphReset.region mode origin transitions) address count) :
    Allowed mode origin address count := by
  have positions:=Listing8ResetLayout.positions mode (Listing8GraphReset.region mode origin transitions)
  simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals cases mode
  all_goals simp only [Allowed,Listing8GraphReset.region,Listing8GraphLayout.reset,Listing8GraphLayout.transition,
    Listing8FullTableImage.start,Listing8FailLayout.endPC,Listing4EntryLayout.mainPC,Listing4EntryLayout.size,
    Listing8JumpLayout.jumpPC,Listing8JumpLayout.callPC,Listing4JumpLayout.prefixSize,StringInit.field,StringCodec.fieldOffset,
    Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at positions ⊢
  all_goals omega

theorem reset (mode : Mode) (origin transitions : Nat)
    (bounds : Listing8ResetLayout.Bounds mode (Listing8GraphReset.region mode origin transitions))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8GraphReset.region mode origin transitions).start)
    (current : Listing8ResetPackets.Initial mode (Listing8GraphReset.region mode origin transitions) state.principal.memory) :
    StringStoreRegions.Run mode (Allowed mode origin)
      ((Listing8ResetLayout.program mode (Listing8GraphReset.region mode origin transitions)).map (StringStoreWrites.liftDword mode)) state :=
  BoundedStoreRegions.monotone mode _ _ _ state (reset_fields mode origin transitions)
    (Listing8ResetStoreRegions.regions mode _ bounds state entry current)

end SmcTuring.Appendix.Listing8GlobalControlRegions
