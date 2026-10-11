module
public import SmcTuring.Appendix.Listing8FailureGlobalImage
public import SmcTuring.Appendix.Listing8FailureValues

public section
namespace SmcTuring.Appendix.Listing8GlobalFailure
open Native Listing8CopyImage Listing8FailureGeometry
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def entryState (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalState.finish mode l t v (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailureImage.finish mode (region mode l sentinel begin) (entryState mode l t v sentinel begin extra seed)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  (Listing8GlobalState.program mode l t v (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed).map StringControl.Form.previous ++
    Listing8FailureTrace.program mode (region mode l sentinel begin) (entryState mode l t v sentinel begin extra seed)

theorem entry (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (entryState mode l t v sentinel begin extra seed).principal.pc=Arithmetic.encodeNat mode (region mode l sentinel begin).start := by
  rw [(positions mode l t sentinel begin bounds).1]
  exact Listing8GlobalState.endpoint mode l t v r owners copies bounds.state (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed

/-- One extended initial image executes every printed instruction through
failure-mask selection and CALL-operand XOR. The stack/CALL itself follows. -/
theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringControl.Trace mode
      (initial mode l v (Listing8PointerImage.backing mode l t
        (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l
          (Listing8FailureGlobalImage.backing mode l sentinel begin extra)))) seed)
      (program mode l t v sentinel begin extra seed) (finish mode l t v sentinel begin extra seed) := by
  have first:=StringControl.previous_trace mode (Listing8GlobalState.trace mode l t v r owners copies bounds.state (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed)
  have last:=Listing8FailureTrace.trace mode (region mode l sentinel begin) (local_bounds mode l t sentinel begin r bounds)
    (entryState mode l t v sentinel begin extra seed) (entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed)
  exact StringControl.trace_append mode first last

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode l t v sentinel begin extra seed).length=if mode=.x86 then 132 else 173 := by
  rw [program,List.length_append,List.length_map,Listing8GlobalState.instruction_count,Listing8FailureTrace.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v sentinel begin extra seed).principal.pc=Arithmetic.encodeNat mode (l.start+(if mode=.x86 then 743 else 1150)) := by
  have pc:=Listing8FailureTrace.endpoint mode (region mode l sentinel begin) (local_bounds mode l t sentinel begin r bounds)
    (entryState mode l t v sentinel begin extra seed) (entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed)
  rw [(positions mode l t sentinel begin bounds).2.1] at pc
  exact pc

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v sentinel begin extra seed).principal.stack=seed.principal.stack ∧
    (finish mode l t v sentinel begin extra seed).sourceIndex=seed.sourceIndex ∧
    (finish mode l t v sentinel begin extra seed).destinationIndex=seed.destinationIndex ∧
    (finish mode l t v sentinel begin extra seed).backwards=false ∧
    (finish mode l t v sentinel begin extra seed).principal.carry=false ∧
    (finish mode l t v sentinel begin extra seed).principal.accumulator=
      StringInit.accumulator mode sentinel (Listing8FailureImage.resetState mode (region mode l sentinel begin)
        (entryState mode l t v sentinel begin extra seed)) := by
  have before:=Listing8GlobalState.registers mode l t v r owners copies bounds.state (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed
  have last:=Listing8FailureValues.registers mode (region mode l sentinel begin) (local_bounds mode l t sentinel begin r bounds)
    (entryState mode l t v sentinel begin extra seed) (entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed)
  exact ⟨last.1.trans before.1,last.2.1.trans before.2.2.1,last.2.2.1.trans before.2.2.2.1,
    last.2.2.2.1.trans before.2.2.2.2.1,last.2.2.2.2.1,last.2.2.2.2.2⟩

end SmcTuring.Appendix.Listing8GlobalFailure
