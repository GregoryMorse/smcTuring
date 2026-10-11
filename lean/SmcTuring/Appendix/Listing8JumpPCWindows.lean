module
public import SmcTuring.Native.StringPCBranches
public import SmcTuring.Appendix.Listing8JumpReturn

public section
namespace SmcTuring.Appendix.Listing8JumpPCWindows
open Native Listing8JumpReturn

/-- Original code placement for both actual CALL outcomes; no runtime PC,
image, readiness, fetch or future target occurs in this certificate. -/
structure Placement (mode : Mode) (start stop origin : Nat) (failed : Bool) : Prop where
  jump : start≤Listing8JumpLayout.jumpPC mode origin ∧ Listing8JumpLayout.failPC mode origin≤stop
  target : start≤Listing8JumpReturn.target mode origin failed ∧
    Listing8JumpReturn.target mode origin failed+Listing4TargetLayout.size mode≤stop

theorem prefix_sequential (mode : Mode) (origin : Nat) :
    ∀ form∈Listing8JumpLayout.prefixForms mode origin,StringPCSteps.Sequential mode form := by
  intro form member
  cases mode with
  | x86 => simp only [Listing8JumpLayout.prefixForms,List.mem_cons,List.not_mem_nil,or_false] at member;subst form;trivial
  | x64 =>
    simp only [Listing8JumpLayout.prefixForms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial

theorem prefix_total (mode : Mode) (origin : Nat) :
    StringPCSteps.total mode (Listing8JumpLayout.prefixForms mode origin)=Listing4JumpLayout.prefixSize mode := by
  cases mode <;> rfl

theorem prefix_guard (mode : Mode) (origin : Nat) :
    StringPCWindows.Guard mode (Listing8JumpLayout.prefixForms mode origin) := by
  cases mode with
  | x86 => change 3≤6 ∧ True;decide
  | x64 => change 3≤22 ∧ 3≤15 ∧ 3≤7 ∧ True;decide

theorem call_size (mode : Mode) (origin : Nat) (failed : Bool) :
    StringPCSteps.size mode (StringStack.native mode (Listing8JumpLayout.call mode origin failed))=5 := rfl

theorem jump (mode : Mode) (start stop origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode ⟨start,stop⟩ (Listing8JumpLayout.forms mode origin failed) state := by
  apply StringPCBranches.last_instruction mode ⟨start,stop⟩ _ _ state (Listing8JumpLayout.jumpPC mode origin)
    (prefix_sequential mode origin) entry (prefix_guard mode origin)
  · rw [call_size];decide
  · exact placed.jump.1
  · rw [prefix_total,call_size]
    exact placed.jump.2
  · exact capacity

theorem target_sequential (mode : Mode) (origin target : Nat) :
    ∀ form∈Listing4TargetLayout.forms mode origin target,StringPCSteps.Sequential mode form := by
  intro form member
  cases mode <;> simp only [Listing4TargetLayout.forms,List.mem_cons,List.not_mem_nil,or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem target_total (mode : Mode) (origin target : Nat) :
    StringPCSteps.total mode (Listing4TargetLayout.forms mode origin target)=Listing4TargetLayout.size mode := by
  cases mode <;> rfl

theorem target_guard (mode : Mode) (origin target : Nat) :
    StringPCWindows.Guard mode (Listing4TargetLayout.forms mode origin target) := by
  cases mode with
  | x86 => change 3≤31 ∧ 3≤25 ∧ 3≤18 ∧ 3≤12 ∧ 3≤6 ∧ True;decide
  | x64 => change 3≤36 ∧ 3≤29 ∧ 3≤21 ∧ 3≤14 ∧ 3≤7 ∧ True;decide

/-- The complete actual target helper is entered at the target PC proved
by the actual preceding CALL effects, for both fail and backedge outcomes. -/
theorem target (mode : Mode) (start stop origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    StringPCWindows.Run mode ⟨start,stop⟩ (Listing4TargetLayout.forms mode origin (Listing8JumpReturn.target mode origin failed))
      (Listing8JumpEffects.finish mode origin failed state) := by
  apply StringPCWindows.sequential mode ⟨start,stop⟩ _ _ (Listing8JumpReturn.target mode origin failed)
    (target_sequential mode origin _)
  · rw [call_shape mode origin failed state entry (by have inside:=placed.jump.2;omega) current]
    rfl
  · exact target_guard mode origin _
  · exact placed.target.1
  · rw [target_total]
    exact placed.target.2
  · exact capacity

theorem complete (mode : Mode) (start stop origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (placed : Placement mode start stop origin failed) (capacity : stop<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    StringPCWindows.Run mode ⟨start,stop⟩ (program mode origin failed) state := by
  have actual:=Listing8JumpTrace.trace mode origin failed state entry (by have inside:=placed.jump.2;omega)
    current.stackImage current.prefixImage current.callImage
  exact StringPCWindows.append_trace mode ⟨start,stop⟩ _ _ state _ actual
    (jump mode start stop origin failed state entry placed capacity)
    (target mode start stop origin failed state entry placed capacity current)

end SmcTuring.Appendix.Listing8JumpPCWindows
