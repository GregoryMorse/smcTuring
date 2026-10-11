module
public import SmcTuring.Appendix.Listing8JumpPCWindows
public import SmcTuring.Appendix.Listing8JumpReturnWrites
public import SmcTuring.Appendix.Listing8TailReadClasses
public import SmcTuring.Native.StringFetchPermissions

public section
namespace SmcTuring.Appendix.Listing8JumpFetch
open Native Listing8JumpReturn
abbrev Placement:=Listing8JumpPCWindows.Placement

theorem actual (mode : Mode) (start stop origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    StringStack.Trace mode state (program mode origin failed) (finish mode origin failed state) :=
  Listing8JumpReturn.trace mode origin failed state entry (by have inside:=placed.jump.2;omega)
    (by have inside:=placed.target.2;omega) current

theorem contained (mode : Mode) (start stop origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    StringFetchWindows.Run mode ⟨start,stop⟩ (program mode origin failed) state :=
  StringFetchWindows.of_pc_run mode ⟨start,stop⟩ (actual mode start stop origin failed state entry placed capacity current)
    (Listing8JumpPCWindows.complete mode start stop origin failed state entry placed capacity current)

theorem complete (mode : Mode) (start stop origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes))
    (stack : start≤origin ∧ origin+Listing4StackLayout.size mode≤stop)
    (current : Current mode origin failed state.principal.memory) :
    StringStack.Trace mode state (program mode origin failed) (finish mode origin failed state) ∧
    StringFetchWindows.Run mode ⟨start,stop⟩ (program mode origin failed) state ∧
    StringWrites.OwnedRun mode start stop (program mode origin failed) state ∧
    StringReadRuns.Run mode ⟨start,stop⟩ (program mode origin failed) state := by
  have owned:=Listing8JumpReturnWrites.owned mode start stop origin failed state entry
    (by have inside:=placed.jump.2;omega) stack current
  exact ⟨actual mode start stop origin failed state entry placed capacity current,
    contained mode start stop origin failed state entry placed capacity current,owned,
    StringReadRuns.local_of_owned mode start stop _ state (Listing8TailReadClasses.jump_return mode origin failed) owned⟩

/-- The target PC, its entire helper window and permissions follow the
actual CALL effect and original placement, for either selected outcome. -/
theorem target_access (mode : Mode) (environment : MappedExecution.Environment) (start stop origin : Nat)
    (mapping : MappedExecution.Mapped mode environment ⟨start,stop⟩)
    (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    StringStack.Trace mode state (Listing8JumpLayout.forms mode origin failed) (Listing8JumpEffects.finish mode origin failed state) ∧
    (Listing8JumpEffects.finish mode origin failed state).principal.pc=Arithmetic.encodeNat mode (target mode origin failed) ∧
    MemoryRegion.Region.Contains ⟨start,stop⟩ (Listing8JumpEffects.finish mode origin failed state).principal.pc.toNat (Listing4TargetLayout.size mode) ∧
    MappedExecution.Window mode environment .execute (Listing8JumpEffects.finish mode origin failed state).principal.pc.toNat (Listing4TargetLayout.size mode) ∧
    MappedExecution.Window mode environment .read (Listing8JumpEffects.finish mode origin failed state).principal.pc.toNat (Listing4TargetLayout.size mode) := by
  have limit : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes) := by have inside:=placed.jump.2;omega
  have located : (Listing8JumpEffects.finish mode origin failed state).principal.pc=Arithmetic.encodeNat mode (target mode origin failed) := by
    rw [call_shape mode origin failed state entry limit current]
    rfl
  have inside : MemoryRegion.Region.Contains ⟨start,stop⟩
      (Listing8JumpEffects.finish mode origin failed state).principal.pc.toNat (Listing4TargetLayout.size mode) := by
    rw [located,Arithmetic.encode_nat_toNat mode _ (by have upper:=placed.target.2;omega)]
    exact placed.target
  exact ⟨Listing8JumpTrace.trace mode origin failed state entry limit current.stackImage current.prefixImage current.callImage,
    located,inside,MappedExecution.window_of_contains mode environment ⟨start,stop⟩ mapping .execute _ _ inside,
    MappedExecution.window_of_contains mode environment ⟨start,stop⟩ mapping .read _ _ inside⟩

theorem next_access (mode : Mode) (environment : MappedExecution.Environment) (start stop origin : Nat)
    (mapping : MappedExecution.Mapped mode environment ⟨start,stop⟩)
    (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes))
    (stack : start≤origin ∧ origin+Listing4StackLayout.size mode≤stop)
    (current : Current mode origin failed state.principal.memory)
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=program mode origin failed) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringFetchWindows.Within mode ⟨start,stop⟩ reached ∧ StringFetchPermissions.Allowed mode environment reached ∧
      StringWrites.CodeWrite mode start stop form reached ∧
      MappedExecution.Window mode environment .write (StringWrites.packet mode form reached).address (StringWrites.packet mode form reached).bytes.length ∧
      StringReadWindows.Within mode ⟨start,stop⟩ form reached ∧ StringReadPermissions.Allowed mode environment form reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after (finish mode origin failed state) := by
  have facts:=complete mode start stop origin failed state entry placed capacity stack current
  exact StringFetchPermissions.next_access mode environment start stop mapping facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 before form after cut

end SmcTuring.Appendix.Listing8JumpFetch
