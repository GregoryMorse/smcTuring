module
public import SmcTuring.Appendix.Listing8DirectionValues

public section
namespace SmcTuring.Appendix.Listing8DirectionSelected
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def value (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Word mode :=
  match mode with
  | .x86 => DwordCode.get memory (pc+6)
  | .x64 => X64.HalfWords.pack (DwordCode.get memory (pc+6)) (DwordCode.get memory (pc+16))

theorem low_result (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory
      (Listing8DirectionLayout.directionPC mode (region mode l)+6) =
      Listing8DirectionMemory.blend v.direction (Listing8DirectionFields.low mode v.back) (Listing8DirectionFields.low mode v.forward) := by
  rw [Listing8GlobalDirection.finish,Listing8DirectionMemory.low_value mode (region mode l) bounds.capacity
    (Listing8GlobalDirection.entryState mode l t v extra seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed),
    Listing8DirectionValues.direction mode l t v r owners copies bounds extra seed,
    Listing8DirectionValues.back_low mode l t v r owners copies bounds extra seed,
    Listing8DirectionValues.forward_low mode l t v r owners copies bounds extra seed]

theorem high_result (l : Layout) (t : Targets) (v : Values .x64) (r : Resources .x64 l)
    (owners : Listing8CopiedOwners.Bounds .x64 l v) (copies : Listing8PointerCopies.Bounds .x64 l t)
    (bounds : Bounds .x64 l t) (extra : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GlobalDirection.finish .x64 l t v extra seed).principal.memory
      (Listing8DirectionLayout.directionPC .x64 (region .x64 l)+16) =
      Listing8DirectionMemory.blend v.direction (X64.HalfWords.high v.back) (X64.HalfWords.high v.forward) := by
  rw [Listing8GlobalDirection.finish,Listing8DirectionMemory.high_value (region .x64 l) bounds.capacity
    (Listing8GlobalDirection.entryState .x64 l t v extra seed) (Listing8GlobalDirection.entry .x64 l t v r owners copies bounds extra seed),
    Listing8DirectionValues.direction .x64 l t v r owners copies bounds extra seed,
    Listing8DirectionValues.back_high l t v r owners copies bounds extra seed,
    Listing8DirectionValues.forward_high l t v r owners copies bounds extra seed]

/-- With the compiler's explicit zero/all-ones direction encoding, the
actual executed prefix selects the complete original neighbor pointer. -/
theorem selected (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (takeBack : Bool) (encoded : v.direction = if takeBack then BitVec.allOnes 32 else 0) :
    value mode (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory
      (Listing8DirectionLayout.directionPC mode (region mode l)) = if takeBack then v.back else v.forward := by
  cases mode with
  | x86 =>
    rw [value,low_result .x86 l t v r owners copies bounds extra seed,encoded,Listing8DirectionMemory.blend_mask]
    cases takeBack <;> rfl
  | x64 =>
    rw [value,low_result .x64 l t v r owners copies bounds extra seed,
      high_result l t v r owners copies bounds extra seed,encoded,Listing8DirectionMemory.blend_mask,Listing8DirectionMemory.blend_mask]
    cases takeBack <;> exact X64.HalfWords.pack_halves _

end SmcTuring.Appendix.Listing8DirectionSelected
