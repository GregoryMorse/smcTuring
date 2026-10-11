module
public import SmcTuring.Appendix.Listing8StateTrace
public import SmcTuring.Native.DwordDataflow
public import SmcTuring.Appendix.Listing8HeadTailMemory

public section
namespace SmcTuring.Appendix.Listing8StateMemory
open Native Listing8StateLayout Listing8StateBounds

theorem memory (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (Listing8StateTrace.finish mode l state).principal.memory =
      DwordDataflow.packetMemory (packets mode l) (DwordDataflow.helperMemory (helpers mode l) state.principal.memory) := by
  rw [Listing8StateTrace.finish,DwordDataflow.packets mode _ _ (packet_chain mode l) (packet_valid mode l bounds) _
    (Listing8StateTrace.helper_endpoint mode l bounds state entry),Listing8StateTrace.helperFinish,
    DwordDataflow.helpers mode _ _ (helper_chain mode l) (helper_valid mode l bounds) state entry]

theorem low_cursor (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    DwordCode.get (Listing8StateTrace.finish mode l state).principal.memory l.cursor =
      DwordCode.get state.principal.memory l.cursor ^^^
        ((DwordCode.get state.principal.memory l.cursor ^^^ DwordCode.get state.principal.memory (newPC mode l+6)) &&&
          DwordCode.get state.principal.memory (maskPC mode l+6)) := by
  rw [memory mode l bounds state entry]
  have before := bounds.cursorBefore
  cases mode <;> simp only [Mode.wordBytes] at before
  all_goals simp (discharger := omega) [DwordDataflow.packetMemory,DwordDataflow.helperMemory,helpers,
    Listing8PointerCopies.split,packets,newPackets,masks,updates,Listing8DirectionLayout.group,
    DwordPackets.raw,DwordArithmetic.result,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc,DwordCode.get_put,DwordDataflow.read_disjoint]

theorem high_cursor (l : Layout) (bounds : Bounds .x64 l)
    (state : StringExecution.State .x64) (entry : state.principal.pc = Arithmetic.encodeNat .x64 l.start) :
    DwordCode.get (Listing8StateTrace.finish .x64 l state).principal.memory (l.cursor+4) =
      DwordCode.get state.principal.memory (l.cursor+4) ^^^
        ((DwordCode.get state.principal.memory (l.cursor+4) ^^^ DwordCode.get state.principal.memory (newPC .x64 l+16)) &&&
          DwordCode.get state.principal.memory (maskPC .x64 l+16)) := by
  rw [memory .x64 l bounds state entry]
  have before := bounds.cursorBefore
  simp only [Mode.wordBytes] at before
  simp (discharger := omega) [DwordDataflow.packetMemory,DwordDataflow.helperMemory,helpers,
    Listing8PointerCopies.split,packets,newPackets,masks,updates,Listing8DirectionLayout.group,
    DwordPackets.raw,DwordArithmetic.result,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc,DwordCode.get_put,DwordDataflow.read_disjoint]

theorem selected (old fresh : BitVec 32) (chosen : Bool) :
    old ^^^ ((old ^^^ fresh) &&& InputUpdate.mask chosen) = if chosen then fresh else old := by
  rw [BitVec.xor_comm old fresh]
  exact Listing8HeadTailMemory.selected old fresh chosen

end SmcTuring.Appendix.Listing8StateMemory
