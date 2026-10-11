module
public import SmcTuring.Appendix.Listing8LoopDirectionImage
public import SmcTuring.Appendix.Listing8MainInputFrames
public import SmcTuring.Appendix.Listing8DirectionPrefixFrames

public section
namespace SmcTuring.Appendix.Listing8LoopDirectionPrefix
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

structure Bounds (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) : Prop where
  input : Listing8MainInput.Bounds mode l t v
  direction : Listing8DirectionGeometry.Bounds mode l t

/-- Both fields describe only the same present main-entry memory. -/
structure Current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (memory : ByteMemory.Memory) : Prop where
  input : Listing8MainInput.Current mode l t v old memory
  direction : Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l) memory

theorem prefix_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t v state).principal.memory w.1 w.2=ByteMemory.bytesAt state.principal.memory w.1 w.2 := by
  have bounds:=b.input.input.prefixBounds
  have codeBefore:=Listing8DirectionPrefixFrames.code_before mode l bounds.resources w member
  have lower:=(Listing8DirectionWindows.window_span mode (Listing8DirectionGeometry.region mode l) w member).1
  change Listing8LiteralInput.endPC mode l.input≤w.1 at lower
  have d:=destinations mode l
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have cursor:=Listing8PointerCopies.cursor_before mode l
  apply Listing8MainPrefixFrames.window mode l t v bounds state entry forward current.input.prefixCurrent w.1 w.2
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · intro site siteMember
    have bound:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site siteMember).2.1
    change site.owner+10≤codeEnd mode l at bound
    exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Listing8DirectionPrefixFrames.direction_store_outside mode l t b.direction w member
  · exact Or.inl (by omega)
  · exact Listing8DirectionPrefixFrames.pointer_outside mode l t b.direction w member

theorem input_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t v state).principal.memory w.1 w.2 :=
  Listing8MainInputFrames.input_window mode l t v old b.input state entry forward current.input w.1 w.2
    (Listing8DirectionPrefixFrames.input_outside mode l t b.direction w member)

theorem window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory w.1 w.2=ByteMemory.bytesAt state.principal.memory w.1 w.2 :=
  (input_window mode l t v old b state entry forward current w member).trans (prefix_window mode l t v old b state entry forward current w member)

/-- All direction/head instruction fragments on the reached state follow
from the actual generic prefix/input writes and the present entry fragments. -/
theorem current_after_input (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l) (Listing8MainInput.finish mode l t v state).principal.memory :=
  Listing8LoopDirectionImage.transport mode _ _ _ current.direction (window mode l t v old b state entry forward current)

end SmcTuring.Appendix.Listing8LoopDirectionPrefix
