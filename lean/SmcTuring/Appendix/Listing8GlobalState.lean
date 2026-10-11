module
public import SmcTuring.Appendix.Listing8StateImage

public section
namespace SmcTuring.Appendix.Listing8GlobalState
open Native Listing8CopyImage Listing8StateGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def entryState (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalHead.finish mode l t v (Listing8StateImage.backing mode l extra) seed
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8StateTrace.finish mode (region mode l) (entryState mode l t v extra seed)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalHead.program mode l t v (Listing8StateImage.backing mode l extra) seed ++
    Listing8StateTrace.program mode (region mode l) (entryState mode l t v extra seed)

theorem entry (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (entryState mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode (region mode l).start := by
  have previous := Listing8GlobalHead.endpoint mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed
  rw [(positions mode l t bounds).1]
  exact previous

/-- The actual M19 pending-pointer copy and XOR/mask/state update extend
the same initialized-image trace, with all current packets derived. -/
theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (initial mode l v
      (Listing8PointerImage.backing mode l t (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra))) seed)
      (program mode l t v extra seed) (finish mode l t v extra seed) := by
  have first := Listing8GlobalHead.trace mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed
  have last := Listing8StateTrace.trace mode (region mode l) (local_bounds mode l t r bounds)
    (entryState mode l t v extra seed) (entry mode l t v r owners copies bounds extra seed)
    (Listing8StateImage.helper_current mode l t v r owners copies bounds extra seed)
    (Listing8StateImage.headers_current mode l t v r owners copies bounds extra seed)
  exact StringDword.trace_append mode first last

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode l t v extra seed).length = if mode = .x86 then 119 else 157 := by
  rw [program,List.length_append,Listing8GlobalHead.instruction_count,Listing8StateTrace.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode (l.start+(if mode = .x86 then 644 else 1028)) := by
  have last := Listing8StateTrace.endpoint mode (region mode l) (local_bounds mode l t r bounds)
    (entryState mode l t v extra seed) (entry mode l t v r owners copies bounds extra seed)
  rw [(positions mode l t bounds).2] at last
  exact last

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.stack = seed.principal.stack ∧
    (finish mode l t v extra seed).principal.carry = false ∧
    (finish mode l t v extra seed).sourceIndex = seed.sourceIndex ∧
    (finish mode l t v extra seed).destinationIndex = seed.destinationIndex ∧
    (finish mode l t v extra seed).backwards = false ∧
    (finish mode l t v extra seed).principal.accumulator = DwordCode.lift mode
      (DwordCode.low mode (Listing8PointerImage.ownerFinish mode l t v
        (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra)) seed).principal.accumulator) := by
  have previous := Listing8GlobalHead.registers mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed
  have last := Listing8StateTrace.registers mode (region mode l) (local_bounds mode l t r bounds)
    (entryState mode l t v extra seed) (entry mode l t v r owners copies bounds extra seed)
  refine ⟨last.2.1.trans previous.1,last.2.2.1,last.2.2.2.1.trans previous.2.2.1,
    last.2.2.2.2.1.trans previous.2.2.2.1,last.2.2.2.2.2.trans previous.2.2.2.2.1,?_⟩
  rw [show (finish mode l t v extra seed).principal.accumulator = _ from last.1,
    entryState,previous.2.2.2.2.2,DwordCode.low_lift]

end SmcTuring.Appendix.Listing8GlobalState
