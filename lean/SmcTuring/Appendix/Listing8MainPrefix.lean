module
public import SmcTuring.Appendix.Listing8MainLiveOwners
public import SmcTuring.Appendix.Listing8InputBounds
public import SmcTuring.Native.StringStack

public section
namespace SmcTuring.Appendix.Listing8MainPrefix
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

/-- Static placement and relocation certificates for an arbitrary pass. -/
structure Bounds (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) : Prop where
  resources : Resources mode l
  owners : Listing8CopiedOwners.Bounds mode l v
  copies : Listing8PointerCopies.Bounds mode l t
  fields : Listing8InputBounds.Fields mode l
  joined : l.input.start=Listing8PointerCopies.endPC mode l
  tapeReach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input)

/-- Only present copy/source declarations and the current pointer helpers. -/
structure Current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (memory : ByteMemory.Memory) : Prop where
  copying : Listing8MainCopyImage.Current mode l v memory
  helpers : ByteMemory.bytesAt memory (codeEnd mode l) (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t

@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8PointerCopies.finish mode l t (Listing8MainLiveOwners.finish mode l v state)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  Listing8MainLiveOwners.program mode l v++Listing8PointerCopies.program mode l t

theorem helper_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    ByteMemory.bytesAt (Listing8MainLiveOwners.finish mode l v state).principal.memory (codeEnd mode l)
      (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t := by
  have d:=destinations mode l
  have extent:=Listing8PointerCopies.bytes_length mode l t
  rw [←b.joined] at extent
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have direction:=b.owners.directionAfter
  rw [Listing8MainLiveOwners.window mode l v b.resources b.owners b.tapeReach state entry forward current.copying _ _
    (Or.inl (by omega)) (Or.inl d.2.2.le)
    (fun site member => Or.inl (by
      have bound:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
      change site.owner+10≤codeEnd mode l at bound;omega))
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
  exact current.helpers

theorem pointer_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    StringDword.Trace mode (Listing8MainLiveOwners.finish mode l v state) (Listing8PointerCopies.program mode l t) (finish mode l t v state) :=
  Listing8PointerCopies.trace mode l t b.copies _
    (Listing8MainLiveOwners.registers mode l v b.resources b.owners b.tapeReach state entry forward current.copying).1
    (helper_current mode l t v b state entry forward current)

/-- One complete generic printed copy/retarget/owner/pointer prefix, with
all intermediate currentness and fetches derived from present main memory. -/
theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    StringDword.Trace mode state (program mode l t v) (finish mode l t v state) :=
  StringDword.trace_append mode (Listing8MainLiveOwners.trace mode l v b.resources b.owners b.tapeReach state entry forward current.copying)
    (pointer_trace mode l t v b state entry forward current)

theorem stack_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    StringStack.Trace mode state (((program mode l t v).map StringControl.Form.previous).map StringStack.Form.previous)
      (finish mode l t v state) :=
  StringStack.previous_trace mode (StringControl.previous_trace mode (trace mode l t v b state entry forward current))

theorem entry (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (atMain : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    (finish mode l t v state).principal.pc=Arithmetic.encodeNat mode l.input.start := by
  have actual:=Listing8PointerCopies.endpoint mode l t b.copies _
    (Listing8MainLiveOwners.registers mode l v b.resources b.owners b.tapeReach state atMain forward current.copying).1
  rw [←b.joined] at actual
  exact actual

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    (finish mode l t v state).principal.stack=state.principal.stack ∧
    (finish mode l t v state).sourceIndex=state.sourceIndex ∧
    (finish mode l t v state).destinationIndex=state.destinationIndex ∧
    (finish mode l t v state).backwards=false ∧
    (finish mode l t v state).principal.carry=false ∧
    (finish mode l t v state).principal.accumulator=
      DwordCode.lift mode (DwordCode.low mode (Listing8MainLiveOwners.finish mode l v state).principal.accumulator) := by
  have prior:=Listing8MainLiveOwners.registers mode l v b.resources b.owners b.tapeReach state entry forward current.copying
  have actual:=Listing8PointerCopies.registers mode l t b.copies _ prior.1
  exact ⟨actual.1.trans prior.2.1,actual.2.2.2.1.trans prior.2.2.1,actual.2.2.2.2.1.trans prior.2.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.2.1,actual.2.1.trans prior.2.2.2.2.2,actual.2.2.1⟩

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    (program mode l t v).length=(if mode=.x86 then 81 else 92) := by
  rw [program,List.length_append,Listing8MainLiveOwners.instruction_count,(Listing8PointerCopies.sizes mode l t).2.2]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8MainPrefix
