module
public import SmcTuring.Appendix.Listing4Entry
public import SmcTuring.Appendix.Listing8JumpPCWindows
public import SmcTuring.Native.StringPCGuards
public import SmcTuring.Native.StringFetchWindows

public section
namespace SmcTuring.Appendix.Listing4EntryFetch
open Native MemoryRegion

theorem sequential (mode : Mode) (origin : Nat) :
    ∀ form∈Listing4EntryLayout.forms mode origin,StringPCSteps.Sequential mode form := by
  simp only [Listing4EntryLayout.forms,List.mem_append]
  intro form member
  rcases member with boot | later
  · have straightBoot : ∀ form∈Listing4Boot.forms mode origin,StringPCSteps.Sequential mode form := by
      cases mode <;> simp [Listing4Boot.forms,Listing4StackLayout.forms,Listing4StackLayout.first,
      Listing4StackLayout.second,Listing4StackLayout.third,Listing4StackLayout.fourth,
      Listing4JumpLayout.forms,Listing4JumpLayout.prefixForms,Listing4JumpLayout.exchange,
      Listing4JumpLayout.adjust,Listing4JumpLayout.exchangeSaved,Listing4JumpLayout.call,
      StackMemory.form,StringStack.native,StringDwordCopy.native,StringPCSteps.Sequential,StringPCSteps.ControlSequential,
      StringPCSteps.DwordSequential,StringPCSteps.StringSequential,StringPCSteps.NativeSequential]
    exact straightBoot form boot
  · exact Listing8JumpPCWindows.target_sequential mode _ _ form later

theorem total (mode : Mode) (origin : Nat) :
    StringPCSteps.total mode (Listing4EntryLayout.forms mode origin)=Listing4EntryLayout.size mode := by
  cases mode <;> rfl

theorem boot_guard (mode : Mode) (origin : Nat) :
    StringPCWindows.Guard mode (Listing4Boot.forms mode origin) := by
  rw [Listing4Boot.forms,Listing4JumpLayout.forms,←List.append_assoc]
  apply StringPCWindows.guard_last
  cases mode <;> change 3≤5 <;> decide

theorem guard (mode : Mode) (origin : Nat) :
    StringPCWindows.Guard mode (Listing4EntryLayout.forms mode origin) :=
  StringPCGuards.append mode _ _ (boot_guard mode origin) (Listing8JumpPCWindows.target_guard mode origin _)

theorem windows (mode : Mode) (region : Region) (origin : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode origin)
    (lower : region.lower≤origin) (upper : Listing4EntryLayout.mainPC mode origin≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode region (Listing4EntryLayout.forms mode origin) state := by
  apply StringPCWindows.sequential mode region _ state origin (sequential mode origin) entry (guard mode origin) lower ?_ capacity
  rw [total]
  exact upper

theorem contained (mode : Mode) (region : Region) (origin : Nat) (seed : StringExecution.State mode)
    (lower : region.lower≤origin) (upper : Listing4EntryLayout.mainPC mode origin≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringFetchWindows.Run mode region (Listing4EntryLayout.forms mode origin) (Listing4Entry.initial mode origin seed) :=
  StringFetchWindows.of_pc_run mode region (Listing4Entry.trace mode origin seed (Nat.lt_of_le_of_lt upper capacity))
    (windows mode region origin _ rfl lower upper capacity)

end SmcTuring.Appendix.Listing4EntryFetch
