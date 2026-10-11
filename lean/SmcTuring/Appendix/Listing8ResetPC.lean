module
public import SmcTuring.Appendix.Listing8DeclarationPC
public import SmcTuring.Native.StringSequentialPackets

public section
namespace SmcTuring.Appendix.Listing8ResetPC
open Native MemoryRegion Listing8ResetLayout

theorem sequential (mode : Mode) (l : Layout) :
    ∀ form∈(program mode l).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [program,List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with (((rfl | inputCopy) | owner) | transitionCopy) | markerMember
  · cases mode <;> trivial
  · exact StringSequentialFamilies.word mode _ form inputCopy
  · have mapped : ((StringInit.forms mode (ownerPC mode l) l.ttape).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)=
        (StringInit.forms mode (ownerPC mode l) l.ttape).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    rw [mapped] at owner
    exact StringSequentialPackets.initializers mode _ _ form owner
  · exact StringSequentialFamilies.word mode _ form transitionCopy
  · exact Listing8OriginalOwnerPC.sequential_form mode (marker mode l) form markerMember

theorem total (mode : Mode) (l : Layout) :
    StringPCSteps.total mode ((program mode l).map (StringStoreWrites.liftDword mode))=(if mode=.x86 then 64 else 89) := by
  cases mode <;> rfl

/-- The actual final ten-byte DOHALT owner supplies the header margin for
the complete reset, including all shorter preceding instructions. -/
theorem guard (mode : Mode) (l : Layout) :
    StringPCWindows.Guard mode ((program mode l).map (StringStoreWrites.liftDword mode)) := by
  unfold program
  rw [List.map_append]
  apply StringPCWindows.guard_prefix mode _ _ (Listing8OriginalOwnerPC.guard_form mode (marker mode l))
  rw [Listing8OriginalOwnerPC.total_form]
  change 3≤10
  decide

theorem windows (mode : Mode) (region : Region) (l : Layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (lower : region.lower≤l.start) (upper : endPC mode l≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode region ((program mode l).map (StringStoreWrites.liftDword mode)) state := by
  apply StringPCWindows.sequential mode region _ state l.start (sequential mode l) entry (guard mode l) lower ?_ capacity
  rw [total,←(positions mode l).2.2.2]
  exact upper

theorem contained (mode : Mode) (region : Region) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory)
    (lower : region.lower≤l.start) (upper : endPC mode l≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringFetchWindows.Run mode region ((program mode l).map (StringStoreWrites.liftDword mode)) state :=
  StringFetchWindows.of_pc_run mode region
    (StringDwordWritesBridge.trace mode (Listing8ResetTrace.trace mode l bounds state entry initial))
    (windows mode region l state entry lower upper capacity)

end SmcTuring.Appendix.Listing8ResetPC
