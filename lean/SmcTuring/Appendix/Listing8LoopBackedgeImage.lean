module
public import SmcTuring.Appendix.Listing8GraphNextDirectionFrames
public import SmcTuring.Appendix.Listing8LoopDirectionImage

public section
namespace SmcTuring.Appendix.Listing8LoopBackedgeImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget Listing8GraphNextDirectionFrames
abbrev Targets:=Listing8PointerCopies.Targets

theorem helper_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory
      (Listing8DirectionGeometry.region mode l).start
      (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (Listing8DirectionGeometry.region mode l))).length=
      DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (Listing8DirectionGeometry.region mode l)) := by
  have member : ((Listing8DirectionGeometry.region mode l).start,
      (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (Listing8DirectionGeometry.region mode l))).length)∈
      Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l) := by
    simp [Listing8DirectionWindows.windows,Listing8DirectionWindows.helper_size]
  rw [Listing8GraphNextDirectionFrames.after_backedge mode origin l t g node rule ctx memory seed _ member,previousDirection,
    Listing8DirectionBodyFrames.direction mode l t (values mode origin g node rule) ctx.resources
      (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head (previousExtra mode origin l g memory)
      (Listing8GlobalBoot.bodySeed mode origin seed) _ member]
  exact Listing8GlobalDirection.helper_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head (previousExtra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed)

theorem arithmetic_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8DirectionLayout.arithmetic mode (Listing8DirectionGeometry.region mode l))
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory := by
  intro reader readerMember
  have member : (reader.pc,6)∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l) := by
    simp only [Listing8DirectionWindows.windows,List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨reader,readerMember,rfl⟩)))
  rw [DwordPackets.Current,Listing8GraphNextDirectionFrames.after_backedge mode origin l t g node rule ctx memory seed _ member,previousDirection,
    Listing8DirectionBodyFrames.direction mode l t (values mode origin g node rule) ctx.resources
      (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head (previousExtra mode origin l g memory)
      (Listing8GlobalBoot.bodySeed mode origin seed) _ member]
  exact Listing8GlobalDirection.arithmetic_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head (previousExtra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) reader readerMember

theorem xor_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory
      (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l))
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l))).length=
      DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l)) := by
  have member : (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l),
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l))).length)∈
      Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l) := by
    simp [Listing8DirectionWindows.windows,Listing8DirectionWindows.xor_size]
  rw [Listing8GraphNextDirectionFrames.after_backedge mode origin l t g node rule ctx memory seed _ member]
  exact Listing8HeadImage.xor_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head (previousExtra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed)

theorem tail_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8DirectionLayout.masks mode (Listing8DirectionGeometry.region mode l)++
      Listing8DirectionLayout.heads mode (Listing8DirectionGeometry.region mode l))
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory := by
  intro reader readerMember
  have member : (reader.pc,6)∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l) := by
    simp only [Listing8DirectionWindows.windows,List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨reader,readerMember,rfl⟩)
  rw [DwordPackets.Current,Listing8GraphNextDirectionFrames.after_backedge mode origin l t g node rule ctx memory seed _ member]
  exact Listing8HeadImage.headers_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head (previousExtra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) reader readerMember

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory :=
  ⟨helper_current mode origin l t g node rule ctx memory seed,
    arithmetic_current mode origin l t g node rule ctx memory seed,
    xor_current mode origin l t g node rule ctx memory seed,
    tail_current mode origin l t g node rule ctx memory seed⟩

end SmcTuring.Appendix.Listing8LoopBackedgeImage
