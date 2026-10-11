module
public import SmcTuring.Appendix.Listing8GraphNextResetOutput
public import SmcTuring.Appendix.Listing8EntryPackets

public section
namespace SmcTuring.Appendix.Listing8GraphNextResetControl
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem jump_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    ByteMemory.bytesAt (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin := by
  let fragment:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have ending:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode fragment=Listing8JumpLayout.jumpPC mode origin at ending
  have coords:=Listing8FailureLayout.positions mode fragment
  have after : fragment.start≤Listing8JumpLayout.jumpPC mode origin := by rw [←ending];omega
  have second:=(Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body).cursorBefore
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤fragment.start at second
  have first:=Listing8StateFields.first_cursor_before mode l t ctx.body.state
  have callAfter : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤Listing8JumpLayout.callPC mode origin+1 := by
    rw [Listing8JumpLayout.prefix_length];dsimp [Listing8JumpLayout.callPC];omega
  rw [Listing8GraphNextReset.effect mode origin l t g node rule target ctx selected memory seed halted,
    StackWindows.word_window _ _ _ _ _ _ (Or.inl (Nat.le_trans second after)),StackWindows.word_window _ _ _ _ _ _ (Or.inl (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr callAfter),
    Listing8GraphNextTable.memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  exact Listing8GraphNextStackImage.jump_prefix mode origin l t g node rule target ctx selected memory seed

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8JumpReturn.Current mode origin false (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory :=
  ⟨Listing8EntryPackets.stack_packet mode origin _ (Listing8GraphNextResetOutput.bootstrap_current mode origin l t g node rule target ctx selected memory seed halted),
    jump_prefix mode origin l t g node rule target ctx selected memory seed halted,
    Listing8GraphNextResetOutput.call_packet mode origin l t g node rule target ctx selected memory seed halted,
    Listing8EntryPackets.begin_packet mode origin _ (Listing8GraphNextResetOutput.bootstrap_current mode origin l t g node rule target ctx selected memory seed halted)⟩

theorem stack_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    MixedMemory.getWord mode (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory (Listing4StackLayout.stptr mode origin)=Arithmetic.encodeNat mode (Listing4StackLayout.stptr mode origin) ∧
    MixedMemory.getWord mode (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory (Listing4StackLayout.returnField mode origin)=Arithmetic.encodeNat mode (Listing4StackLayout.stptr mode origin) := by
  have code:=Listing8GraphNextResetOutput.bootstrap_current mode origin l t g node rule target ctx selected memory seed halted
  have fits:=Listing8JumpLayout.stack_capacity mode origin (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
  exact ⟨Listing8EntryPackets.stptr mode origin _ fits code,Listing8EntryPackets.return_field mode origin _ fits code⟩

end SmcTuring.Appendix.Listing8GraphNextResetControl
