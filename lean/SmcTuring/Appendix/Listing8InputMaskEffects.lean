module
public import SmcTuring.Appendix.Listing8InputMask

public section
namespace SmcTuring.Appendix.Listing8InputMaskEffects
open Native Listing8LiteralInput
abbrev Dword := BitVec 32

theorem cursor (mode : Mode) (layout : Layout) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) :
    MixedMemory.getWord mode (Listing8InputMask.normalized mode layout state).memory layout.cursor =
      MixedMemory.getWord mode state.memory layout.cursor :=
  Listing8LiteralComposition.cursor_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0

theorem symbol (mode : Mode) (layout : Layout) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) :
    DwordCode.get (Listing8InputMask.normalized mode layout state).memory (layout.head+6) =
      DwordCode.get state.memory (layout.head+6) :=
  Listing8LiteralComposition.tape_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0

theorem endpoint (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.memory)
    (bound : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (value : DwordCode.get state.memory (layout.head+6) = tape) :
    (Listing8LiteralComposition.finish mode layout rule tape fresh state).pc = Arithmetic.encodeNat mode (endPC mode layout) := by
  rw [Listing8InputMask.finish_same mode layout rule tape fresh capacity state entry,
    Listing8SourceEffects.effect mode layout rule tape pending fresh capacity masks update outside
      (Listing8InputMask.normalized mode layout state) entry
      (Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask _ current)
      ((cursor mode layout outside state).trans bound) ((symbol mode layout outside state).trans value)]

theorem registers (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.memory)
    (bound : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (value : DwordCode.get state.memory (layout.head+6) = tape) :
    (Listing8LiteralComposition.finish mode layout rule tape fresh state).accumulator = DwordCode.lift mode (DwordCode.low mode state.accumulator) ∧
    (Listing8LiteralComposition.finish mode layout rule tape fresh state).stack = state.stack ∧
    (Listing8LiteralComposition.finish mode layout rule tape fresh state).carry = false := by
  rw [Listing8InputMask.finish_same mode layout rule tape fresh capacity state entry]
  exact Listing8SourceEffects.registers mode layout rule tape pending fresh capacity masks update outside
    (Listing8InputMask.normalized mode layout state) entry
    (Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask _ current)
    ((cursor mode layout outside state).trans bound) ((symbol mode layout outside state).trans value)

theorem destination_values (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (separate : Listing8LiteralMaskTrace.Separate mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.memory)
    (bound : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (value : DwordCode.get state.memory (layout.head+6) = tape)
    (reader : DwordLayout.Layout) (member : reader ∈ distributionLayouts mode layout) :
    DwordCode.get (Listing8LiteralComposition.finish mode layout rule tape fresh state).memory reader.destination =
      InputUpdate.mask (chosen rule tape) := by
  rw [Listing8InputMask.finish_same mode layout rule tape fresh capacity state entry]
  exact Listing8SourceEffects.destination_values mode layout rule tape pending fresh capacity masks separate update outside
    (Listing8InputMask.normalized mode layout state) entry
    (Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask _ current)
    ((cursor mode layout outside state).trans bound) ((symbol mode layout outside state).trans value) reader member

end SmcTuring.Appendix.Listing8InputMaskEffects
