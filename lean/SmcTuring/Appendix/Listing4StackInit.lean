module
public import SmcTuring.Appendix.Listing4StackLayout

public section
namespace SmcTuring.Appendix.Listing4StackInit
open Native LittleEndian Listing4StackLayout
@[expose] def swapped (start : Nat) (state : StringExecution.State .x64) :=
  StringStack.execute .x64 (StringStack.native .x64 (first start)) state
@[expose] def restored (start : Nat) (state : StringExecution.State .x64) :=
  StringStack.execute .x64 (StringStack.native .x64 (second start)) (swapped start state)
@[expose] def stored (start : Nat) (state : StringExecution.State .x64) :=
  StringStack.execute .x64 (StringStack.native .x64 (third start)) (restored start state)
@[expose] def finish (mode : Mode) (start : Nat) (state : StringExecution.State mode) : StringExecution.State mode :=
  match mode with
  | .x86 => StringExecution.run .x86 (StringInit.forms .x86 start (stptr .x86 start)) state
  | .x64 => StringStack.execute .x64 (StringStack.native .x64 (fourth start)) (stored start state)
@[expose] def accumulator (mode : Mode) (start : Nat) (state : StringExecution.State mode) : Word mode :=
  match mode with | .x86 => state.principal.accumulator | .x64 => Arithmetic.encodeNat .x64 (stptr .x64 start)

theorem swapped_effect (start : Nat) (state : StringExecution.State .x64)
    (entry : state.principal.pc = Arithmetic.encodeNat .x64 start)
    (fits : start+34 < 2^64)
    (current : ByteMemory.bytesAt state.principal.memory start 34 = bytes .x64 start) :
    swapped start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat .x64 (start+7)
      accumulator := Arithmetic.encodeNat .x64 (stptr .x64 start)
      memory := ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start) state.principal.accumulator}} := by
  have targetFits : stptr .x64 start < 2^64 := by dsimp [stptr];omega
  have effect := WordMemoryArithmetic.located_effect .x64 .exchange start (stptr .x64 start) state.principal entry
    (by intro _;dsimp [WordMemoryArithmetic.size,wordPrefix,stptr];unfold Relocation.SignedDelta Relocation.delta;omega) targetFits
  change Execution.execute .x64 (first start) state.principal = _ at effect
  rw [initial_stptr .x64 start state.principal.memory fits current] at effect
  rw [swapped,StringStack.native_execute,effect];rfl

theorem restored_effect (start : Nat) (state : StringExecution.State .x64)
    (entry : state.principal.pc = Arithmetic.encodeNat .x64 start)
    (fits : start+34 < 2^64)
    (current : ByteMemory.bytesAt state.principal.memory start 34 = bytes .x64 start) :
    restored start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat .x64 (start+14)
      accumulator := Arithmetic.encodeNat .x64 (stptr .x64 start)}} := by
  have firstEffect := swapped_effect start state entry fits current
  have pc : (swapped start state).principal.pc = Arithmetic.encodeNat .x64 (start+7) := by rw [firstEffect]
  have targetFits : stptr .x64 start < 2^64 := by dsimp [stptr];omega
  have effect := StackMemory.store_acc_effect .x64 (start+7) (stptr .x64 start) (swapped start state).principal pc
    (by intro _;dsimp [StackMemory.size,wordPrefix,stptr];unfold Relocation.SignedDelta Relocation.delta;omega) targetFits
  change Execution.execute .x64 (second start) (swapped start state).principal = _ at effect
  have back : ByteMemory.putWord .x64
      (ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start) state.principal.accumulator)
      (stptr .x64 start) (Arithmetic.encodeNat .x64 (stptr .x64 start)) = state.principal.memory := by
    rw [Writes.put_word_overwrite,←initial_stptr .x64 start state.principal.memory fits current,MixedMemory.put_get_back]
  rw [restored,StringStack.native_execute,effect,firstEffect]
  simp only [show StackMemory.size .x64=7 from rfl,show start+7+7=start+14 by omega,back]

theorem stored_effect (start : Nat) (state : StringExecution.State .x64)
    (entry : state.principal.pc = Arithmetic.encodeNat .x64 start)
    (fits : start+34 < 2^64)
    (current : ByteMemory.bytesAt state.principal.memory start 34 = bytes .x64 start) :
    stored start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat .x64 (start+24)
      accumulator := Arithmetic.encodeNat .x64 (stptr .x64 start)}} := by
  have previous := restored_effect start state entry fits current
  have pc : (restored start state).principal.pc = Arithmetic.encodeNat .x64 (start+14) := by rw [previous]
  have targetFits : stptr .x64 start < 2^64 := by dsimp [stptr];omega
  have effect := StackMemory.moffs_effect .x64 (start+14) (stptr .x64 start) (restored start state).principal pc targetFits
  change Execution.execute .x64 (third start) (restored start state).principal = _ at effect
  have back : ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start)
      (Arithmetic.encodeNat .x64 (stptr .x64 start)) = state.principal.memory := by
    rw [←initial_stptr .x64 start state.principal.memory fits current,MixedMemory.put_get_back]
  rw [stored,StringStack.native_execute,effect,previous]
  simp only [show Native.moffsOperandOffset .x64=2 from rfl,show Mode.x64.wordBytes=8 from rfl,show start+14+2+8=start+24 by omega,back]

theorem effect (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : start+size mode < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode) = bytes mode start) :
    finish mode start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (start+size mode)
      accumulator := accumulator mode start state}} := by
  cases mode with
  | x86 => exact StringInit.effect .x86 start (stptr .x86 start) state entry fits current
  | x64 =>
    have previous := stored_effect start state entry fits current
    have pc : (stored start state).principal.pc = Arithmetic.encodeNat .x64 (start+24) := by rw [previous]
    have targetFits : stptr .x64 start < 2^64 := by dsimp [stptr];change start+34<2^64 at fits;omega
    have callEffect := StackMemory.moffs_effect .x64 (start+24) (stptr .x64 start) (stored start state).principal pc targetFits
    change Execution.execute .x64 (fourth start) (stored start state).principal = _ at callEffect
    have back : ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start)
        (Arithmetic.encodeNat .x64 (stptr .x64 start)) = state.principal.memory := by
      rw [←initial_stptr .x64 start state.principal.memory fits current,MixedMemory.put_get_back]
    rw [finish,StringStack.native_execute,callEffect,previous]
    simp only [show Native.moffsOperandOffset .x64=2 from rfl,show Mode.x64.wordBytes=8 from rfl,show start+24+2+8=start+34 by omega,back]
    rfl

/-- Initial packet reads and executed stores derive the reusable stack pointer. -/
theorem stptr_value (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : start+size mode < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode) = bytes mode start) :
    MixedMemory.getWord mode (finish mode start state).principal.memory (stptr mode start) =
      Arithmetic.encodeNat mode (stptr mode start) := by
  rw [effect mode start state entry fits current]
  exact initial_stptr mode start state.principal.memory fits current
theorem svptr_value (start : Nat) (state : StringExecution.State .x64)
    (entry : state.principal.pc = Arithmetic.encodeNat .x64 start)
    (fits : start+34 < 2^64)
    (current : ByteMemory.bytesAt state.principal.memory start 34 = bytes .x64 start) :
    MixedMemory.getWord .x64 (finish .x64 start state).principal.memory (returnField .x64 start) =
      Arithmetic.encodeNat .x64 (stptr .x64 start) := by
  rw [effect .x64 start state entry fits current]
  exact initial_svptr start state.principal.memory fits current
end SmcTuring.Appendix.Listing4StackInit
