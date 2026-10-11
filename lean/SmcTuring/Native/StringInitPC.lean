module
public import SmcTuring.Native.StringSequentialPackets
public import SmcTuring.Native.StringPCWindows

public section
namespace SmcTuring.Native.StringInitPC
open MemoryRegion

theorem total (mode : Mode) (pc value : Nat) :
    StringPCSteps.total mode ((StringInit.forms mode pc value).map (StringWrites.liftString mode))=StringCodec.initialSize mode := by
  cases mode <;> rfl

theorem guard (mode : Mode) (pc value : Nat) :
    StringPCWindows.Guard mode ((StringInit.forms mode pc value).map (StringWrites.liftString mode)) := by
  cases mode
  · change 3≤10 ∧ True;decide
  · change 3≤27 ∧ 3≤20 ∧ 3≤13 ∧ 3≤10 ∧ True;decide

theorem windows (mode : Mode) (region : Region) (pc value : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (lower : region.lower≤pc) (upper : pc+StringCodec.initialSize mode≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode region ((StringInit.forms mode pc value).map (StringWrites.liftString mode)) state := by
  apply StringPCWindows.sequential mode region _ state pc
    (StringSequentialPackets.initializers mode pc value) entry (guard mode pc value) lower ?_ capacity
  rw [total]
  exact upper

end SmcTuring.Native.StringInitPC
