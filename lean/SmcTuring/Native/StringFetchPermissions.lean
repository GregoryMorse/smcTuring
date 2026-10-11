module
public import SmcTuring.Native.StringFetchWindows
public import SmcTuring.Native.StringReadPermissions

public section
namespace SmcTuring.Native.StringFetchPermissions
open MemoryRegion MappedExecution

/-- Each actual decoder request has canonical bytes with effective read and
execute permission. Physical realization of the mapping remains explicit. -/
@[expose] def Allowed (mode : Mode) (environment : Environment) (state : StringExecution.State mode) : Prop :=
  ∀ count∈StringFetchRequests.requests mode state.principal.memory state.principal.pc.toNat,
    Window mode environment .execute state.principal.pc.toNat count ∧
    Window mode environment .read state.principal.pc.toNat count

theorem of_contained (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) (state : StringExecution.State mode)
    (contained : StringFetchWindows.Within mode region state) : Allowed mode environment state := by
  intro count requested
  have inside:=contained count requested
  exact ⟨window_of_contains mode environment region mapping .execute _ _ inside,
    window_of_contains mode environment region mapping .read _ _ inside⟩

theorem next_request (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (windows : StringFetchWindows.Run mode region forms state) (before : List (StringStack.Form mode))
    (form : StringStack.Form mode) (after : List (StringStack.Form mode)) (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringFetchWindows.Within mode region reached ∧ Allowed mode environment reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after finish := by
  obtain ⟨reached,leading,current,inside,tail⟩:=StringFetchWindows.next_request mode region actual windows before form after cut
  exact ⟨reached,leading,current,inside,of_contained mode environment region mapping reached inside,tail⟩

/-- Fetch/classifier, data-read and complete-store certificates refer to the
same actual prefix state, with no second trace or future packet premise. -/
theorem next_access (mode : Mode) (environment : Environment) (start stop : Nat)
    (mapping : Mapped mode environment ⟨start,stop⟩) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (windows : StringFetchWindows.Run mode ⟨start,stop⟩ forms state)
    (owned : StringWrites.OwnedRun mode start stop forms state)
    (reads : StringReadRuns.Run mode ⟨start,stop⟩ forms state)
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringFetchWindows.Within mode ⟨start,stop⟩ reached ∧ Allowed mode environment reached ∧
      StringWrites.CodeWrite mode start stop form reached ∧
      Window mode environment .write (StringWrites.packet mode form reached).address (StringWrites.packet mode form reached).bytes.length ∧
      StringReadWindows.Within mode ⟨start,stop⟩ form reached ∧ StringReadPermissions.Allowed mode environment form reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after finish := by
  obtain ⟨reached,leading,current,inside,allowed,tail⟩:=next_request mode environment ⟨start,stop⟩ mapping actual windows before form after cut
  rw [←cut,StringWrites.owned_run_append,StringWrites.trace_run_eq mode leading] at owned
  rw [←cut,StringReadRuns.append,StringWrites.trace_run_eq mode leading] at reads
  have store:=owned.2.1
  have read:=reads.2.1
  exact ⟨reached,leading,current,inside,allowed,store,
    window_of_contains mode environment ⟨start,stop⟩ mapping .write _ _ ⟨store.2.1,store.2.2⟩,
    read,StringReadPermissions.of_contained mode environment ⟨start,stop⟩ mapping form reached read,tail⟩

end SmcTuring.Native.StringFetchPermissions
