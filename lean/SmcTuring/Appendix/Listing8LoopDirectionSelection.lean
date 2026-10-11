module
public import SmcTuring.Appendix.Listing8LoopDirectionValues

public section
namespace SmcTuring.Appendix.Listing8LoopDirectionSelection
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopDirection.Bounds
abbrev Current:=Listing8LoopDirection.Current

theorem low_result (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    DwordCode.get (Listing8LoopDirection.finish mode l t v state).principal.memory (Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l)+6)=
      Listing8DirectionMemory.blend v.direction (Listing8DirectionFields.low mode v.back) (Listing8DirectionFields.low mode v.forward) := by
  rw [Listing8LoopDirection.finish,Listing8DirectionMemory.low_value mode (Listing8DirectionGeometry.region mode l) b.direction.capacity
    (Listing8MainInput.finish mode l t v state) (Listing8MainInput.endpoint mode l t v old b.input state entry forward current.input),
    Listing8LoopDirectionValues.direction mode l t v old b state entry forward current,Listing8LoopDirectionValues.back_low mode l t v old b state entry forward current,
    Listing8LoopDirectionValues.forward_low mode l t v old b state entry forward current]

theorem high_result (l : Layout) (t : Targets) (v : Values .x64) (old : OldInput) (b : Bounds .x64 l t v)
    (state : StringExecution.State .x64) (entry : state.principal.pc=Arithmetic.encodeNat .x64 l.start)
    (forward : state.backwards=false) (current : Current .x64 l t v old state.principal.memory) :
    DwordCode.get (Listing8LoopDirection.finish .x64 l t v state).principal.memory (Listing8DirectionLayout.directionPC .x64 (Listing8DirectionGeometry.region .x64 l)+16)=
      Listing8DirectionMemory.blend v.direction (X64.HalfWords.high v.back) (X64.HalfWords.high v.forward) := by
  rw [Listing8LoopDirection.finish,Listing8DirectionMemory.high_value (Listing8DirectionGeometry.region .x64 l) b.direction.capacity
    (Listing8MainInput.finish .x64 l t v state) (Listing8MainInput.endpoint .x64 l t v old b.input state entry forward current.input),
    Listing8LoopDirectionValues.direction .x64 l t v old b state entry forward current,Listing8LoopDirectionValues.back_high l t v old b state entry forward current,
    Listing8LoopDirectionValues.forward_high l t v old b state entry forward current]

theorem selected (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (takeBack : Bool)
    (encoded : v.direction=(if takeBack then BitVec.allOnes 32 else 0)) :
    Listing8DirectionSelected.value mode (Listing8LoopDirection.finish mode l t v state).principal.memory (Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l))=
      if takeBack then v.back else v.forward := by
  cases mode with
  | x86 =>
    rw [Listing8DirectionSelected.value,low_result .x86 l t v old b state entry forward current,encoded,Listing8DirectionMemory.blend_mask]
    cases takeBack <;> rfl
  | x64 =>
    rw [Listing8DirectionSelected.value,low_result .x64 l t v old b state entry forward current,
      high_result l t v old b state entry forward current,encoded,Listing8DirectionMemory.blend_mask,Listing8DirectionMemory.blend_mask]
    cases takeBack <;> exact X64.HalfWords.pack_halves _

end SmcTuring.Appendix.Listing8LoopDirectionSelection
