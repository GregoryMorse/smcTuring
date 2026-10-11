module
public import SmcTuring.Appendix.Listing8HeadTailTrace
public import SmcTuring.Native.DwordDataflow

public section
namespace SmcTuring.Appendix.Listing8HeadTailMemory
open Native Listing8DirectionLayout Listing8HeadTailBounds

theorem memory (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l)) :
    (Listing8HeadTailTrace.finish mode l state).principal.memory =
      DwordDataflow.packetMemory (heads mode l) (DwordDataflow.packetMemory (masks mode l)
        (DwordXorSequence.writes (xorLayouts mode l) state.principal.memory)) := by
  rw [Listing8HeadTailTrace.finish,DwordDataflow.packets mode _ _ (heads_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_right _ member)) _
    (Listing8HeadTailTrace.mask_endpoint mode l bounds state entry)]
  rw [Listing8HeadTailTrace.maskFinish,DwordDataflow.packets mode _ _ (masks_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_left _ member)) _
    (Listing8HeadTailTrace.xor_endpoint mode l bounds state entry),Listing8HeadTailTrace.xorFinish,
    DwordXorSequence.memory_effect mode _ _ (xor_chain mode l) (xor_valid mode l bounds) state entry]

theorem low_cursor (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l)) :
    DwordCode.get (Listing8HeadTailTrace.finish mode l state).principal.memory l.cursor =
      DwordCode.get state.principal.memory l.cursor ^^^
        ((DwordCode.get state.principal.memory (directionPC mode l+6) ^^^ DwordCode.get state.principal.memory l.cursor) &&&
          DwordCode.get state.principal.memory (maskPC mode l+6)) := by
  rw [memory mode l bounds state entry]
  have before := bounds.cursorBefore
  cases mode <;> simp only [Mode.wordBytes] at before
  all_goals simp (discharger := omega) [DwordDataflow.packetMemory,DwordXorSequence.writes,xorLayouts,masks,heads,group,
    DwordPackets.raw,DwordArithmetic.result,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,
    copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,
    Nat.add_assoc,DwordCode.get_put,DwordDataflow.read_disjoint]

theorem high_cursor (l : Layout) (bounds : Bounds .x64 l)
    (state : StringExecution.State .x64) (entry : state.principal.pc = Arithmetic.encodeNat .x64 (selectionEnd .x64 l)) :
    DwordCode.get (Listing8HeadTailTrace.finish .x64 l state).principal.memory (l.cursor+4) =
      DwordCode.get state.principal.memory (l.cursor+4) ^^^
        ((DwordCode.get state.principal.memory (directionPC .x64 l+16) ^^^ DwordCode.get state.principal.memory (l.cursor+4)) &&&
          DwordCode.get state.principal.memory (maskPC .x64 l+16)) := by
  rw [memory .x64 l bounds state entry]
  have before := bounds.cursorBefore
  simp only [Mode.wordBytes] at before
  simp (discharger := omega) [DwordDataflow.packetMemory,DwordXorSequence.writes,xorLayouts,masks,heads,group,
    DwordPackets.raw,DwordArithmetic.result,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,
    copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,
    Nat.add_assoc,DwordCode.get_put,DwordDataflow.read_disjoint]

theorem selected (old fresh : BitVec 32) (chosen : Bool) :
    old ^^^ ((fresh ^^^ old) &&& InputUpdate.mask chosen) = if chosen then fresh else old := by
  cases chosen with
  | false => simp [InputUpdate.mask]
  | true =>
    change old ^^^ ((fresh ^^^ old) &&& BitVec.allOnes 32) = fresh
    rw [BitVec.and_allOnes]
    rw [BitVec.xor_comm fresh old,←BitVec.xor_assoc,BitVec.xor_self]
    simp

end SmcTuring.Appendix.Listing8HeadTailMemory
