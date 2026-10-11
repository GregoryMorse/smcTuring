module
public import SmcTuring.Native.StringReadRuns

public section
namespace SmcTuring.Native.StringReadPermissions
open MemoryRegion MappedExecution

/-- Canonical addresses and effective read permission for every byte of the
computed actual data-read window. A form without a data read needs none. -/
@[expose] def Allowed (mode : Mode) (environment : Environment) (form : StringStack.Form mode)
    (state : StringExecution.State mode) : Prop :=
  match StringReadWindows.read mode form state with
  | none => True
  | some packet => Window mode environment .read packet.address packet.count

theorem of_contained (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) (form : StringStack.Form mode) (state : StringExecution.State mode)
    (contained : StringReadWindows.Within mode region form state) : Allowed mode environment form state := by
  unfold Allowed
  cases window : StringReadWindows.read mode form state with
  | none => trivial
  | some packet =>
    exact window_of_contains mode environment region mapping .read _ _
      (by simpa only [StringReadWindows.Within,StringReadWindows.Contained,window] using contained)

theorem next_read (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (reads : StringReadRuns.Run mode region forms state) (before : List (StringStack.Form mode))
    (form : StringStack.Form mode) (after : List (StringStack.Form mode)) (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringReadWindows.Within mode region form reached ∧ Allowed mode environment form reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after finish := by
  obtain ⟨reached,leading,current,contained,tail⟩:=StringReadRuns.next_read mode region actual reads before form after cut
  exact ⟨reached,leading,current,contained,of_contained mode environment region mapping form reached contained,tail⟩

/-- Read and complete-store permissions share exactly the state reached by
the same actual prefix; no future read packet or second trace is assumed. -/
theorem next_access (mode : Mode) (environment : Environment) (start stop : Nat)
    (mapping : Mapped mode environment ⟨start,stop⟩) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (owned : StringWrites.OwnedRun mode start stop forms state)
    (reads : StringReadRuns.Run mode ⟨start,stop⟩ forms state)
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringWrites.CodeWrite mode start stop form reached ∧
      Window mode environment .write (StringWrites.packet mode form reached).address (StringWrites.packet mode form reached).bytes.length ∧
      StringReadWindows.Within mode ⟨start,stop⟩ form reached ∧ Allowed mode environment form reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after finish := by
  obtain ⟨reached,leading,current,contained,allowed,tail⟩:=next_read mode environment ⟨start,stop⟩ mapping actual reads before form after cut
  rw [←cut,StringWrites.owned_run_append,StringWrites.trace_run_eq mode leading] at owned
  have store:=owned.2.1
  exact ⟨reached,leading,current,store,
    window_of_contains mode environment ⟨start,stop⟩ mapping .write _ _ ⟨store.2.1,store.2.2⟩,
    contained,allowed,tail⟩

end SmcTuring.Native.StringReadPermissions
