module
public import SmcTuring.Appendix.Listing9Storage
public import SmcTuring.Native.StringInitPC
public import SmcTuring.Native.StringPCGuards
public import SmcTuring.Native.StringFetchWindows

public section
namespace SmcTuring.Appendix.Listing9StorageFetch
open Native Listing9PackedLayout

theorem mapped (mode : Mode) (start transitions nodes : Nat) :
    Listing9Storage.program mode start transitions nodes=
      (Listing9Storage.forms mode start transitions nodes).map (StringWrites.liftString mode) := by
  simp only [Listing9Storage.program,List.map_map]
  rfl

theorem sequential (mode : Mode) (start transitions nodes : Nat) :
    ∀ form∈Listing9Storage.program mode start transitions nodes,StringPCSteps.Sequential mode form := by
  rw [mapped,Listing9Storage.forms,List.map_append]
  intro form member
  rcases List.mem_append.mp member with save | pointer
  · exact StringSequentialPackets.initializers mode _ _ form save
  · exact StringSequentialPackets.initializers mode _ _ form pointer

theorem total (mode : Mode) (start transitions nodes : Nat) :
    saveOwner mode start transitions nodes+StringPCSteps.total mode (Listing9Storage.program mode start transitions nodes)=
      endPC mode start transitions nodes := by
  cases mode <;> rfl

theorem guard (mode : Mode) (start transitions nodes : Nat) :
    StringPCWindows.Guard mode (Listing9Storage.program mode start transitions nodes) := by
  rw [mapped,Listing9Storage.forms,List.map_append]
  exact StringPCGuards.append mode _ _ (StringInitPC.guard mode _ _) (StringInitPC.guard mode _ _)

theorem windows (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes)) :
    StringPCWindows.Run mode ⟨saveOwner mode start transitions nodes,endPC mode start transitions nodes⟩
      (Listing9Storage.program mode start transitions nodes) state :=
  StringPCWindows.sequential mode _ _ state _ (sequential mode start transitions nodes) entry (guard mode start transitions nodes)
    (Nat.le_refl _) (Nat.le_of_eq (total mode start transitions nodes)) bounds.capacity

theorem contained (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Listing9Storage.Current mode start transitions nodes state.principal.memory) :
    StringFetchWindows.Run mode ⟨saveOwner mode start transitions nodes,endPC mode start transitions nodes⟩
      (Listing9Storage.program mode start transitions nodes) state :=
  StringFetchWindows.of_pc_run mode _ (Listing9Storage.trace mode start transitions nodes bounds state entry current)
    (windows mode start transitions nodes bounds state entry)

end SmcTuring.Appendix.Listing9StorageFetch
