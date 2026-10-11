module
public import SmcTuring.Appendix.Listing8BootControl

public section
namespace SmcTuring.Appendix.Listing8GlobalBootValues
open Native Listing8CopyImage Listing8GlobalBoot
abbrev Targets:=Listing8PointerCopies.Targets
theorem transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel backing seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next :=
  Listing8FailureGlobalValues.transition mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _
theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (takeBack : Bool) (encoded : v.direction=if takeBack then BitVec.allOnes 32 else 0) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel backing seed).principal.memory l.input.cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then (if takeBack then v.back else v.forward) else Arithmetic.encodeNat mode l.sourceNode :=
  Listing8FailureGlobalValues.head mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _ takeBack encoded
theorem tape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (finish mode origin l t v sentinel backing seed).principal.memory (l.sourceNode+6)=
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape :=
  Listing8FailureGlobalValues.tape mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _
theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel backing seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t v sentinel backing seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t v sentinel backing seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t v sentinel backing seed).backwards=false ∧
    (finish mode origin l t v sentinel backing seed).principal.carry=false ∧
    (finish mode origin l t v sentinel backing seed).principal.accumulator=
      StringInit.accumulator mode sentinel (Listing8FailureImage.resetState mode (Listing8BootControl.region mode origin l sentinel)
        (Listing8GlobalFailure.entryState mode l t v sentinel (Listing8BootImage.beginPC mode origin) (extra mode origin backing) (bodySeed mode origin seed))) :=
  Listing8GlobalFailure.registers mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _
end SmcTuring.Appendix.Listing8GlobalBootValues
