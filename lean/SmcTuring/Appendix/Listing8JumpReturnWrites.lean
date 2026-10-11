module
public import SmcTuring.Appendix.Listing8JumpReturn
public import SmcTuring.Appendix.Listing4TargetWrites

public section
namespace SmcTuring.Appendix.Listing8JumpReturnWrites
open Native Listing8JumpReturn

theorem target_owned (mode : Mode) (codeStart codeEnd origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (inside : codeStart≤origin ∧ origin+Listing4StackLayout.size mode≤codeEnd)
    (current : Current mode origin failed state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd (Listing4TargetLayout.forms mode origin (target mode origin failed))
      (Listing8JumpEffects.finish mode origin failed state) := by
  rw [call_shape mode origin failed state entry capacity current]
  exact Listing4TargetWrites.owned mode codeStart codeEnd origin (target mode origin failed)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin state)
    (ranges mode origin failed) (Listing8JumpLayout.stack_capacity mode origin capacity) inside current.stackImage

theorem owned (mode : Mode) (codeStart codeEnd origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (inside : codeStart≤origin ∧ origin+Listing4StackLayout.size mode≤codeEnd)
    (current : Current mode origin failed state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd (program mode origin failed) state := by
  unfold program
  exact StackFieldWrites.owned_append mode codeStart codeEnd (Listing8JumpLayout.forms mode origin failed)
    (Listing4TargetLayout.forms mode origin (target mode origin failed)) state (Listing8JumpEffects.finish mode origin failed state)
    (Listing8JumpTrace.trace mode origin failed state entry capacity current.stackImage current.prefixImage current.callImage)
    (Listing8JumpWrites.owned mode codeStart codeEnd origin failed state entry capacity inside current.stackImage)
    (target_owned mode codeStart codeEnd origin failed state entry capacity inside current)

theorem execute (mode : Mode) (codeStart codeEnd origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (targetFits : target mode origin failed+Listing4TargetLayout.size mode<2^(8*mode.wordBytes))
    (inside : codeStart≤origin ∧ origin+Listing4StackLayout.size mode≤codeEnd)
    (current : Current mode origin failed state.principal.memory) :
    StringStack.Trace mode state (program mode origin failed) (finish mode origin failed state) ∧
    StringWrites.OwnedRun mode codeStart codeEnd (program mode origin failed) state :=
  ⟨Listing8JumpReturn.trace mode origin failed state entry capacity targetFits current,
    owned mode codeStart codeEnd origin failed state entry capacity inside current⟩

end SmcTuring.Appendix.Listing8JumpReturnWrites
