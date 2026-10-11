module
public import SmcTuring.Appendix.Listing8OriginalOwnerPC
public import SmcTuring.Native.StringFetchWindows

public section
namespace SmcTuring.Appendix.Listing8DeclarationPC
open Native MemoryRegion Listing8Prototypes

theorem nodes_sequential (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) :
    ∀ form∈(Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode),
      StringPCSteps.Sequential mode form := by
  induction table generalizing start with
  | nil => simp [Listing8NodeTrace.program]
  | cons value table ih =>
    simp only [Listing8NodeTrace.program,List.map_append,List.mem_append]
    intro form member
    rcases member with first | later
    · exact Listing8OriginalOwnerPC.sequential mode (Listing8NodeBlock.owners mode start value) form first
    · exact ih _ form later

theorem transitions_sequential (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) :
    ∀ form∈(Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode),
      StringPCSteps.Sequential mode form := by
  induction table generalizing start with
  | nil => simp [Listing8TableTrace.program]
  | cons value table ih =>
    simp only [Listing8TableTrace.program,List.map_append,List.mem_append]
    intro form member
    rcases member with first | later
    · exact Listing8OriginalOwnerPC.sequential mode (Listing8TransitionBlock.owners mode start value) form first
    · exact ih _ form later

/-- The byte extent, not an instruction-count bound, controls arbitrarily
large finite declaration tables. -/
theorem nodes_total (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) :
    StringPCSteps.total mode ((Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode))=
      table.length*nodeSpan mode := by
  induction table generalizing start with
  | nil => simp [Listing8NodeTrace.program,StringPCSteps.total]
  | cons value table ih =>
    rw [Listing8NodeTrace.program,List.map_append,StringPCSteps.total_append,Listing8NodeBlock.program,
      Listing8OriginalOwnerPC.total,Listing8NodeBlock.total,ih]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem transitions_total (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) :
    StringPCSteps.total mode ((Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode))=
      table.length*transitionSpan mode := by
  induction table generalizing start with
  | nil => simp [Listing8TableTrace.program,StringPCSteps.total]
  | cons value table ih =>
    rw [Listing8TableTrace.program,List.map_append,StringPCSteps.total_append,Listing8TransitionBlock.program,
      Listing8OriginalOwnerPC.total,Listing8TransitionBlock.total,ih]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem nodes_guard (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) :
    StringPCWindows.Guard mode ((Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode)) := by
  induction table generalizing start with
  | nil => trivial
  | cons value table ih =>
    rw [Listing8NodeTrace.program,List.map_append]
    exact StringPCGuards.append mode _ _
      (Listing8OriginalOwnerPC.guard mode (Listing8NodeBlock.owners mode start value)) (ih _)

theorem transitions_guard (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) :
    StringPCWindows.Guard mode ((Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode)) := by
  induction table generalizing start with
  | nil => trivial
  | cons value table ih =>
    rw [Listing8TableTrace.program,List.map_append]
    exact StringPCGuards.append mode _ _
      (Listing8OriginalOwnerPC.guard mode (Listing8TransitionBlock.owners mode start value)) (ih _)

theorem nodes_windows (mode : Mode) (region : Region) (start : Nat) (table : List (Listing8NodeBlock.Values mode))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (lower : region.lower≤start) (upper : Listing8NodeTable.endPC mode start table≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode region ((Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode)) state := by
  apply StringPCWindows.sequential mode region _ state start (nodes_sequential mode start table) entry
    (nodes_guard mode start table) lower ?_ capacity
  rw [nodes_total]
  exact upper

theorem transitions_windows (mode : Mode) (region : Region) (start : Nat) (table : List (Listing8CopyImage.Values mode))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (lower : region.lower≤start) (upper : Listing8TransitionTable.endPC mode start table≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode region ((Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode)) state := by
  apply StringPCWindows.sequential mode region _ state start (transitions_sequential mode start table) entry
    (transitions_guard mode start table) lower ?_ capacity
  rw [transitions_total]
  exact upper

theorem nodes_contained (mode : Mode) (region : Region) (start : Nat) (table : List (Listing8NodeBlock.Values mode))
    (valid : Listing8NodeTable.Valid mode start table) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8NodeTable.Initial mode start table state.principal.memory)
    (lower : region.lower≤start) (upper : Listing8NodeTable.endPC mode start table≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringFetchWindows.Run mode region ((Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode)) state :=
  StringFetchWindows.of_pc_run mode region
    (StringDwordWritesBridge.trace mode (Listing8NodeTrace.trace mode start table valid state entry initial))
    (nodes_windows mode region start table state entry lower upper capacity)

theorem transitions_contained (mode : Mode) (region : Region) (start : Nat) (table : List (Listing8CopyImage.Values mode))
    (valid : Listing8TransitionTable.Valid mode start table) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8TransitionTable.Initial mode start table state.principal.memory)
    (lower : region.lower≤start) (upper : Listing8TransitionTable.endPC mode start table≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringFetchWindows.Run mode region ((Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode)) state :=
  StringFetchWindows.of_pc_run mode region
    (StringDwordWritesBridge.trace mode (Listing8TableTrace.trace mode start table valid state entry initial))
    (transitions_windows mode region start table state entry lower upper capacity)

end SmcTuring.Appendix.Listing8DeclarationPC
