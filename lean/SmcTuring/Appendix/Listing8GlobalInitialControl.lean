module
public import SmcTuring.Appendix.Listing8GlobalControlBindings
public import SmcTuring.Appendix.Listing8GlobalMainBounds
public import SmcTuring.Appendix.Listing8LoopOriginalImage
public import SmcTuring.Appendix.Listing8GraphCopyWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalInitialControl
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory
      origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin :=
  Listing4Entry.initial_current mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)

theorem prefix_image (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory
      (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin := by
  let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have endEq:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode region=Listing8JumpLayout.jumpPC mode origin at endEq
  have callEq:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode region=Listing8JumpLayout.callPC mode origin at callEq
  have coords:=Listing8FailureLayout.positions mode region
  have after : region.start≤Listing8JumpLayout.jumpPC mode origin := by
    have bound:=coords.2.2.2.1;rw [endEq] at bound;omega
  have upper : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤Listing8FailureLayout.callPC mode region+5 := by
    rw [callEq,Listing8JumpLayout.prefix_length];change Listing8JumpLayout.callPC mode origin≤Listing8JumpLayout.callPC mode origin+5;omega
  rw [Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed,
    initialMemory,Listing8FailureGlobalImage.image_window mode l t _ _ _ ctx.resources ctx.body _ _ _ after upper]
  rw [Listing8FailureGlobalImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    change region.start+(Listing8FailureLayout.bytes mode region).length≤_
    rw [Listing8FailureGlobalImage.region_end];exact Nat.le_of_eq endEq)),
    byte_frame _ _ _ _ _ (Or.inr (by rw [callEq,Listing8JumpLayout.prefix_length];exact Nat.le_refl _))]
  rw [extra,Listing8GlobalBoot.extra,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing4EntryLayout.bytes_length]
    cases mode <;> dsimp [Listing4EntryLayout.size,Listing8JumpLayout.jumpPC] <;> omega))]
  exact ByteMemory.bytes_at_put _ _ _

theorem call_image (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory
      (Listing8JumpLayout.callPC mode origin) 5=Native.encode mode (Listing8JumpLayout.call mode origin false) := by
  rw [Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed]
  have packet:=Listing8FailureGlobalImage.initial_call mode l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.resources ctx.body (extra mode origin l g memory)
  have callEq:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at callEq
  change ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory)
    (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) 5=
    Native.encode mode (.callRelative (Listing8FailureLayout.original mode
      (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))) at packet
  rw [Listing8FailureLayout.original,callEq] at packet
  exact packet

theorem fail_image (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory
      (Listing8JumpLayout.failPC mode origin) (Listing4TargetLayout.size mode)=Listing8FailLayout.bytes mode origin := by
  let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have endEq:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode region=Listing8JumpLayout.jumpPC mode origin at endEq
  have callEq:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode region=Listing8JumpLayout.callPC mode origin at callEq
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  have coords:=Listing8FailureLayout.positions mode region
  have after : region.start≤Listing8JumpLayout.failPC mode origin := by
    have bound:=coords.2.2.2.1;rw [endEq] at bound;omega
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have nodeAfter : Listing8JumpLayout.failPC mode origin+Listing4TargetLayout.size mode≤l.sourceNode := by omega
  have ruleAfter : Listing8JumpLayout.failPC mode origin+Listing4TargetLayout.size mode≤l.sourceTransition := by omega
  rw [Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed,initialMemory,
    Listing8LateFrames.initial_image mode l t _ _ _ ctx.resources ctx.body _ _ _ after (Or.inr nodeAfter) (Or.inr ruleAfter)]
  rw [Listing8FailureGlobalImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    change region.start+(Listing8FailureLayout.bytes mode region).length≤_
    rw [Listing8FailureGlobalImage.region_end,endEq];omega)),
    byte_frame _ _ _ _ _ (Or.inl (by
      change Listing8FailureLayout.callPC mode region+(Listing8FailureGlobalImage.callBytes mode l _ _).length≤_
      have size : (Listing8FailureGlobalImage.callBytes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).length=5 := by cases mode <;> rfl
      rw [size,callEq];exact Nat.le_of_eq ordering.2.2.2.2.1))]
  rw [extra,Listing8GlobalBoot.extra,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing4EntryLayout.bytes_length]
    have beginEnd:=ordering.2.1
    have entrySize : origin+Listing4EntryLayout.size mode=Listing4EntryLayout.mainPC mode origin := rfl
    omega)),Listing8JumpImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8JumpLayout.prefix_length]
      change Listing8JumpLayout.callPC mode origin≤Listing8JumpLayout.failPC mode origin
      omega))]
  simpa only [Listing8FailImage.backing,Listing8FailLayout.bytes_length] using
    ByteMemory.bytes_at_put _ (Listing8JumpLayout.failPC mode origin) (Listing8FailLayout.bytes mode origin)

/-- All original control fragments come from the complete one-time emitted
image after every graph/body/bootstrap overlay, with no byte observation input. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GlobalControlLayout.Current mode origin
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory := by
  have stack:=Listing4Entry.stack_current mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
  have begin:=Listing4Entry.target_current mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
  exact ⟨stack,prefix_image mode origin l t g node rule ctx memory seed,
    RelativeCallTemplate.initial mode _ _ _ (call_image mode origin l t g node rule ctx memory seed),begin,
    fail_image mode origin l t g node rule ctx memory seed⟩

theorem decodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GlobalControlTemplates.Decodes mode origin
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory :=
  Listing8GlobalControlTemplates.decodes mode origin _
    (Listing8GlobalControlTemplates.initial mode origin _ (current mode origin l t g node rule ctx memory seed))

end SmcTuring.Appendix.Listing8GlobalInitialControl
