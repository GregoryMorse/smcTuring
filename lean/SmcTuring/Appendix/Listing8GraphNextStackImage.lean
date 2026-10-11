module
public import SmcTuring.Appendix.Listing8GraphNextEarlyBody

public section
namespace SmcTuring.Appendix.Listing8GraphNextStackImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem code_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory origin (Listing4EntryLayout.size mode)=
      Listing4EntryLayout.bytes mode origin := by
  rw [Listing8GraphNextEarlyBody.failure mode origin l t g node rule target ctx selected memory seed origin (Listing4EntryLayout.size mode)
    (by rw [ctx.boot.packed];rfl),Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact Listing8StackMetadata.code_current mode origin l t (values mode origin g node rule) _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
    (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed

theorem stack_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory origin (Listing4StackLayout.size mode)=
      Listing4StackLayout.bytes mode origin := by
  have current:=code_current mode origin l t g node rule target ctx selected memory seed
  have first:=ByteWindow.packet (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory origin [] (Listing4Boot.bytes mode origin)
    (Listing4TargetLayout.bytes mode origin (Listing4JumpLayout.beginPC mode origin)) (by
      simp only [List.nil_append]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact current)
  have code : ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory origin (Listing4Boot.size mode)=Listing4Boot.bytes mode origin := by
    simpa only [List.length_nil,Nat.add_zero,Listing4Boot.bytes_length] using first
  exact Listing4Boot.stack_packet mode origin _ code

theorem begin_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8BootImage.beginPC mode origin) (Listing4TargetLayout.size mode)=Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
  have current:=code_current mode origin l t g node rule target ctx selected memory seed
  have packet:=ByteWindow.packet (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory origin
    (Listing4Boot.bytes mode origin) (Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin)) [] (by
      simp only [List.append_nil]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact current)
  have typed : ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory
      (origin+Listing4Boot.size mode) (Listing4TargetLayout.size mode)=Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
    simpa only [Listing4Boot.bytes_length,Listing4TargetLayout.bytes_length] using packet
  rw [←Listing4Boot.endpoint] at typed
  exact typed

theorem jump_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin := by
  let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have endEq:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode region=Listing8JumpLayout.jumpPC mode origin at endEq
  have callEq:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode region=Listing8JumpLayout.callPC mode origin at callEq
  have coords:=Listing8FailureLayout.positions mode region
  have after : region.start≤Listing8JumpLayout.jumpPC mode origin := by
    rw [←endEq];omega
  have upper : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤Listing8FailureLayout.callPC mode region+5 := by
    rw [callEq,Listing8JumpLayout.prefix_length]
    dsimp [Listing8JumpLayout.callPC];omega
  have andBefore : Listing8FailureLayout.andPC mode region+10≤Listing8JumpLayout.jumpPC mode origin := by
    rw [←endEq];simp only [Listing8FailureLayout.endPC,Listing8FailureLayout.xorPC];omega
  have maskBefore : Listing8FailureLayout.mask mode region+4≤Listing8JumpLayout.jumpPC mode origin := by
    rw [←endEq];simp only [Listing8FailureLayout.mask,Listing8FailureLayout.endPC];omega
  have callAfter : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤Listing8FailureLayout.callPC mode region := by
    rw [callEq,Listing8JumpLayout.prefix_length];rfl
  rw [Listing8GraphNextFailure.finish,Listing8FailureReuseEffects.window mode region
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
    _ _ (Or.inl andBefore) (Or.inl maskBefore) (Or.inr (by omega)),
    Listing8GraphNextFailureImage.window mode origin l t g node rule target ctx selected memory seed _ _ after upper,
    Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact Listing8JumpImage.current mode origin l t (values mode origin g node rule) _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed

end SmcTuring.Appendix.Listing8GraphNextStackImage
