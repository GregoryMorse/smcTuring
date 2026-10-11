module
public import SmcTuring.Appendix.Listing8GraphNextStateImage
public import SmcTuring.Appendix.Listing8LoopStateImage

public section
namespace SmcTuring.Appendix.Listing8LoopBackedgeStateImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextStateImage
abbrev Targets:=Listing8PointerCopies.Targets

theorem helper_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory (Listing8StateGeometry.region mode l).start
      (DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l))).length=
      DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l)) := by
  have member : ((Listing8StateGeometry.region mode l).start,
      (DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l))).length)∈
      Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l) := by
    cases mode <;> simp [Listing8StateGeometry.windows,DwordMixedSequence.bytes,Listing8StateLayout.helpers,Listing8PointerCopies.split,
      DwordMixedImage.bytes_length,DwordLayout.span,DwordLayout.storeSize]
  rw [Listing8GraphNextStateImage.after_backedge mode origin l t g node rule ctx memory seed _ member]
  exact Listing8StateImage.helper_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state (previousExtra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)

theorem headers_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l))
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory := by
  intro reader readerMember
  have member : (reader.pc,6)∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l) := by
    cases mode
    all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
      Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at readerMember
    all_goals rcases readerMember with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Listing8StateGeometry.windows]
  rw [DwordPackets.Current,Listing8GraphNextStateImage.after_backedge mode origin l t g node rule ctx memory seed _ member]
  exact Listing8StateImage.headers_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state (previousExtra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) reader readerMember

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory :=
  ⟨helper_current mode origin l t g node rule ctx memory seed,headers_current mode origin l t g node rule ctx memory seed⟩

end SmcTuring.Appendix.Listing8LoopBackedgeStateImage
