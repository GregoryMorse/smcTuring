module
public import SmcTuring.Appendix.Listing8GraphNextDirectionValues

public section
namespace SmcTuring.Appendix.Listing8GraphNextDirectionSelection
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem low_result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l)+6)=
      Listing8DirectionMemory.blend (liveValues mode origin g node rule target).direction (Listing8DirectionFields.low mode (liveValues mode origin g node rule target).back) (Listing8DirectionFields.low mode (liveValues mode origin g node rule target).forward) := by
  rw [Listing8GraphNextDirection.finish,Listing8DirectionMemory.low_value mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity
    (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed) (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed),
    Listing8GraphNextDirectionValues.direction mode origin l t g node rule target ctx selected memory seed,Listing8GraphNextDirectionValues.back_low mode origin l t g node rule target ctx selected memory seed,
    Listing8GraphNextDirectionValues.forward_low mode origin l t g node rule target ctx selected memory seed]

theorem high_result (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context .x64 origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GraphNextDirection.finish .x64 origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.directionPC .x64 (Listing8DirectionGeometry.region .x64 l)+16)=
      Listing8DirectionMemory.blend (liveValues .x64 origin g node rule target).direction (X64.HalfWords.high (liveValues .x64 origin g node rule target).back) (X64.HalfWords.high (liveValues .x64 origin g node rule target).forward) := by
  rw [Listing8GraphNextDirection.finish,Listing8DirectionMemory.high_value (Listing8DirectionGeometry.region .x64 l) ctx.body.state.head.capacity
    (Listing8GraphNextInput.finish .x64 origin l t g node rule target memory seed) (Listing8GraphNextInput.endpoint .x64 origin l t g node rule target ctx selected memory seed),
    Listing8GraphNextDirectionValues.direction .x64 origin l t g node rule target ctx selected memory seed,Listing8GraphNextDirectionValues.back_high origin l t g node rule target ctx selected memory seed,
    Listing8GraphNextDirectionValues.forward_high origin l t g node rule target ctx selected memory seed]

theorem selected (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8DirectionSelected.value mode (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l))=
      if (g.rules target).takeBack then (liveValues mode origin g node rule target).back else (liveValues mode origin g node rule target).forward := by
  have encoded : (liveValues mode origin g node rule target).direction=(if (g.rules target).takeBack then BitVec.allOnes 32 else 0) := rfl
  cases mode with
  | x86 =>
    rw [Listing8DirectionSelected.value,low_result .x86 origin l t g node rule target ctx selected memory seed,encoded,Listing8DirectionMemory.blend_mask]
    cases (g.rules target).takeBack <;> rfl
  | x64 =>
    rw [Listing8DirectionSelected.value,low_result .x64 origin l t g node rule target ctx selected memory seed,
      high_result origin l t g node rule target ctx selected memory seed,encoded,Listing8DirectionMemory.blend_mask,Listing8DirectionMemory.blend_mask]
    cases (g.rules target).takeBack <;> exact X64.HalfWords.pack_halves _

end SmcTuring.Appendix.Listing8GraphNextDirectionSelection
