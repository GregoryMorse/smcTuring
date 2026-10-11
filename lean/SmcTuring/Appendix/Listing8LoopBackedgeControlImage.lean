module
public import SmcTuring.Appendix.Listing8LoopControlImage
public import SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure
public import SmcTuring.Appendix.Listing8GraphNextStackImage

public section
namespace SmcTuring.Appendix.Listing8LoopBackedgeControlImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem entry_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin := by
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact Listing8StackMetadata.code_current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
    (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed

theorem prefix_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin := by
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact Listing8JumpImage.current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopControlImage.Current mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t
      (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) := by
  refine ⟨Listing8LoopGraphBackedgeFailure.current mode origin l t g node rule target ctx selected memory seed,
    entry_packet mode origin l t g node rule ctx memory seed,prefix_packet mode origin l t g node rule ctx memory seed,?_,Listing8GraphNextFailImage.after_backedge mode origin l t g node rule ctx memory seed⟩
  have packet:=Listing8GraphNextCallImage.after_backedge mode origin l t g node rule target ctx selected memory seed
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at position
  rw [Listing8FailureLayout.original,position] at packet
  exact packet

end SmcTuring.Appendix.Listing8LoopBackedgeControlImage
