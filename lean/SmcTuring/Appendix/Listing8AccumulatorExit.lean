module
public import SmcTuring.Appendix.Listing8AccumulatorBody

public section
namespace SmcTuring.Appendix.Listing8AccumulatorExit
open Native

/-- These observations all refer to the same present epilogue-entry memory.
The later second and third fetches are proved after actual pointer writes. -/
structure Current (mode : Mode) (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) : Prop where
  first : ByteMemory.bytesAt memory a.epilogue (Native.encode mode (AccumulatorLayout.first mode a)).length=Native.encode mode (AccumulatorLayout.first mode a)
  second : ByteMemory.bytesAt memory (AccumulatorLayout.secondPC mode a) (Native.encode mode (AccumulatorLayout.second mode a)).length=Native.encode mode (AccumulatorLayout.second mode a)
  third : ByteMemory.bytesAt memory (AccumulatorLayout.thirdPC mode a) (Native.encode mode (AccumulatorLayout.third mode a)).length=Native.encode mode (AccumulatorLayout.third mode a)

@[expose] def finish (mode : Mode) (a : AccumulatorLayout.Layout) (state : StringExecution.State mode) :=
  {state with principal:=AccumulatorEffects.finish mode a state.principal}
@[expose] def program (mode : Mode) (a : AccumulatorLayout.Layout) := (AccumulatorLayout.program mode a).map (StringStack.native mode)

theorem trace (mode : Mode) (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (pointerAfter : AccumulatorLayout.endPC mode a≤a.pointer)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode a.epilogue)
    (current : Current mode a state.principal.memory) :
    StringStack.Trace mode state (program mode a) (finish mode a state) := by
  let first : StringExecution.State mode:={state with principal:=AccumulatorEffects.swapped mode a state.principal}
  let second : StringExecution.State mode:={state with principal:=AccumulatorEffects.restored mode a state.principal}
  have firstFits : a.epilogue<2^(8*mode.wordBytes) := by
    have cap:=valid.epilogueFits;unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC at cap;omega
  have secondFits : AccumulatorLayout.secondPC mode a<2^(8*mode.wordBytes) := by
    have cap:=valid.epilogueFits;unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC at cap;omega
  have thirdFits : AccumulatorLayout.thirdPC mode a<2^(8*mode.wordBytes) := by
    have cap:=valid.epilogueFits;unfold AccumulatorLayout.endPC at cap;omega
  have aFetch : StringStack.fetch mode state.principal.memory state.principal.pc.toNat=some (StringStack.native mode (AccumulatorLayout.first mode a)) := by
    rw [entry,Arithmetic.encode_nat_toNat mode _ firstFits]
    exact StringStack.native_encoding mode _ _ _ current.first
  have secondPacket : ByteMemory.bytesAt first.principal.memory (AccumulatorLayout.secondPC mode a) (Native.encode mode (AccumulatorLayout.second mode a)).length=Native.encode mode (AccumulatorLayout.second mode a) := by
    have endBefore : AccumulatorLayout.secondPC mode a+(Native.encode mode (AccumulatorLayout.second mode a)).length≤a.pointer := by
      rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.1]
      have third:=show AccumulatorLayout.secondPC mode a+AccumulatorLayout.storeSize mode=AccumulatorLayout.thirdPC mode a from rfl
      have ending:=show AccumulatorLayout.thirdPC mode a+AccumulatorLayout.exchangeSize mode=AccumulatorLayout.endPC mode a from rfl
      omega
    change ByteMemory.bytesAt (AccumulatorEffects.swapped mode a state.principal).memory _ _=_
    rw [AccumulatorEffects.swapped,Reader.exchange_effect mode _ _ _ (AccumulatorLayout.first_hits mode a valid state.principal entry),
      AccumulatorLayout.pointer_toNat mode a valid,StackWindows.word_window _ _ _ _ _ _ (Or.inr endBefore)]
    exact current.second
  have bFetch : StringStack.fetch mode first.principal.memory first.principal.pc.toNat=some (StringStack.native mode (AccumulatorLayout.second mode a)) := by
    rw [AccumulatorEffects.swapped_pc mode a valid state.principal entry,Arithmetic.encode_nat_toNat mode _ secondFits]
    exact StringStack.native_encoding mode _ _ _ secondPacket
  have thirdPacket : ByteMemory.bytesAt second.principal.memory (AccumulatorLayout.thirdPC mode a) (Native.encode mode (AccumulatorLayout.third mode a)).length=Native.encode mode (AccumulatorLayout.third mode a) := by
    rw [show second.principal.memory=state.principal.memory from AccumulatorEffects.restored_memory mode a valid state.principal entry]
    exact current.third
  have cFetch : StringStack.fetch mode second.principal.memory second.principal.pc.toNat=some (StringStack.native mode (AccumulatorLayout.third mode a)) := by
    rw [AccumulatorEffects.restored_pc mode a valid state.principal entry,Arithmetic.encode_nat_toNat mode _ thirdFits]
    exact StringStack.native_encoding mode _ _ _ thirdPacket
  change StringStack.Trace mode state [StringStack.native mode (AccumulatorLayout.first mode a),StringStack.native mode (AccumulatorLayout.second mode a),StringStack.native mode (AccumulatorLayout.third mode a)] _
  refine .step aFetch ?_
  rw [StringStack.native_execute]
  change StringStack.Trace mode first [StringStack.native mode (AccumulatorLayout.second mode a),StringStack.native mode (AccumulatorLayout.third mode a)] _
  refine .step bFetch ?_
  rw [StringStack.native_execute]
  change StringStack.Trace mode second [StringStack.native mode (AccumulatorLayout.third mode a)] _
  refine .step cFetch ?_
  rw [StringStack.native_execute]
  exact .nil _

theorem effect (mode : Mode) (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode a.epilogue)
    (original : Word mode) (saved : Execution.load mode state.principal.memory (Arithmetic.encodeNat mode a.save)=original)
    (pointer : Execution.load mode state.principal.memory (Arithmetic.encodeNat mode a.pointer)=Arithmetic.encodeNat mode a.save) :
    finish mode a state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (AccumulatorLayout.endPC mode a)
      accumulator:=original
      memory:=ByteMemory.putWord mode state.principal.memory a.save (Arithmetic.encodeNat mode a.save)}} := by
  rw [finish,AccumulatorEffects.correct mode a valid state.principal entry original saved pointer]

end SmcTuring.Appendix.Listing8AccumulatorExit
