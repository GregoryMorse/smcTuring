module
public import SmcTuring.Appendix.Listing8FailTransition

public section
namespace SmcTuring.Appendix.Listing8RetainedInputSource
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets

/-- The original itapeptr packet survives the actual failure comparison and
all three persistent failure-mask/CALL writes. Its current bytes are derived
from the maintained preceding image, not supplied at the reset entry. -/
theorem current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel begin)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory
      (Listing8FailureLayout.ownerPC (Listing8FailureGeometry.region mode l sentinel begin))
      (StringCodec.initialSize mode)=
      StringInit.bytes mode (Listing8FailureLayout.ownerPC (Listing8FailureGeometry.region mode l sentinel begin)) sentinel := by
  let fragment:=Listing8FailureGeometry.region mode l sentinel begin
  have initial:=Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies body extra seed
  rw [Listing8GlobalFailure.finish,Listing8FailureValues.window mode fragment
    (Listing8FailureGeometry.local_bounds mode l t sentinel begin r body) _
    (Listing8GlobalFailure.entry mode l t v sentinel begin r owners copies body extra seed) initial
    (Listing8FailureLayout.ownerPC fragment) (StringCodec.initialSize mode)
    (Or.inr (by dsimp [Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,
      Listing8FailureLayout.notPC,Listing8FailureLayout.comparisonPC];omega))
    (Or.inr (by dsimp [Listing8FailureLayout.mask,Listing8FailureLayout.xorPC,
      Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,Listing8FailureLayout.notPC,
      Listing8FailureLayout.comparisonPC];omega))
    (Or.inr (by dsimp [Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,
      Listing8FailureLayout.xorPC,Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,
      Listing8FailureLayout.notPC,Listing8FailureLayout.comparisonPC];omega))]
  exact Listing8FailureImage.owner_current mode fragment _ initial

theorem body_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalJump.bodyEnd mode origin l t v sentinel memory seed).principal.memory
      (Listing8FailureLayout.ownerPC (Listing8BootControl.region mode origin l sentinel))
      (StringCodec.initialSize mode)=
      StringInit.bytes mode (Listing8FailureLayout.ownerPC (Listing8BootControl.region mode origin l sentinel)) sentinel :=
  current mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _

theorem body_value (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GlobalJump.bodyEnd mode origin l t v sentinel memory seed).principal.memory
      (Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel))=
      Arithmetic.encodeNat mode sentinel := by
  let fragment:=Listing8BootControl.region mode origin l sentinel
  have cap:=Listing8FailureBounds.owner_fits mode fragment
    (Listing8FailureGeometry.local_bounds mode l t sentinel (Listing8BootImage.beginPC mode origin) r body)
  have fits : Listing8FailureLayout.source mode fragment<2^(8*mode.wordBytes) := by
    have ending:=Listing8FailureLayout.source_end mode fragment
    change Listing8FailureLayout.comparisonPC mode fragment<_ at cap
    have positive : 0<mode.wordBytes := by cases mode <;> decide
    omega
  have value:=StringInit.initialized_pointer mode (Listing8FailureLayout.ownerPC fragment) sentinel _ cap
    (body_current mode origin l t v sentinel r owners copies body memory seed)
  change Execution.load mode _ (Arithmetic.encodeNat mode (Listing8FailureLayout.source mode fragment))=_ at value
  rw [MixedMemory.load_nat mode _ _ fits] at value
  exact value

theorem after_ttape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8FailTransition.finish mode origin l t v sentinel memory seed).principal.memory
      (Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel))=
      Arithmetic.encodeNat mode sentinel := by
  rw [(Listing8FailTransition.result mode origin l t v sentinel r owners copies boot body located block memory seed).2.1]
  exact body_value mode origin l t v sentinel r owners copies body _ seed
end SmcTuring.Appendix.Listing8RetainedInputSource
