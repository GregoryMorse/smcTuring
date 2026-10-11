module
public import SmcTuring.Appendix.Listing8BeginReturn

public section
namespace SmcTuring.Appendix.Listing8BeginValues
open Native Listing8CopyImage Listing8BeginReturn
abbrev Targets:=Listing8PointerCopies.Targets
theorem transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next := by
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed]
  exact Listing8GlobalBootValues.transition mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin memory) seed
theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (takeBack : Bool) (encoded : v.direction=if takeBack then BitVec.allOnes 32 else 0) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory l.input.cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then (if takeBack then v.back else v.forward) else Arithmetic.encodeNat mode l.sourceNode := by
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed]
  exact Listing8GlobalBootValues.head mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin memory) seed takeBack encoded
theorem tape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (finish mode origin l t v sentinel memory seed).principal.memory (l.sourceNode+6)=
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed]
  exact Listing8GlobalBootValues.tape mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin memory) seed
theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t v sentinel memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t v sentinel memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t v sentinel memory seed).backwards=false ∧
    (finish mode origin l t v sentinel memory seed).principal.carry=false ∧
    (finish mode origin l t v sentinel memory seed).principal.accumulator=(Listing8GlobalJump.bodyEnd mode origin l t v sentinel memory seed).principal.accumulator := by
  have prior:=Listing8GlobalBootValues.registers mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin memory) seed
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed]
  exact ⟨prior.1,prior.2.1,prior.2.2.1,prior.2.2.2.1,rfl,rfl⟩
end SmcTuring.Appendix.Listing8BeginValues
