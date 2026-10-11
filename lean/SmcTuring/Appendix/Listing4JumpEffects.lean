module
public import SmcTuring.Appendix.Listing4JumpLayout

public section
namespace SmcTuring.Appendix.Listing4JumpEffects
open Native LittleEndian Listing4StackLayout Listing4JumpLayout
@[expose] def exchanged (mode : Mode) (start : Nat) (state : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (exchange mode start)) (Listing4StackInit.finish mode start state)
@[expose] def adjusted (start : Nat) (state : StringExecution.State .x64) :=
  StringStack.execute .x64 (adjust start) (exchanged .x64 start state)
@[expose] def prefixEnd (mode : Mode) (start : Nat) (state : StringExecution.State mode) : StringExecution.State mode :=
  match mode with
  | .x86 => exchanged .x86 start state
  | .x64 => StringStack.execute .x64 (StringStack.native .x64 (exchangeSaved start)) (adjusted start state)
@[expose] def finish (mode : Mode) (start : Nat) (state : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (call mode)) (prefixEnd mode start state)
@[expose] def flag (mode : Mode) (start : Nat) (state : StringExecution.State mode) : Bool :=
  match mode with
  | .x86 => state.principal.carry
  | .x64 => BitVec.uaddOverflow (Arithmetic.encodeNat .x64 (stptr .x64 start)) (Arithmetic.encodeNat .x64 18)

theorem exchanged_effect (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : beginPC mode start < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode) = Listing4StackLayout.bytes mode start) :
    exchanged mode start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (jumpPC mode start+StackMemory.size mode)
      accumulator := Listing4StackInit.accumulator mode start state
      stack := Arithmetic.encodeNat mode (stptr mode start)
      memory := ByteMemory.putWord mode state.principal.memory (stptr mode start) state.principal.stack}} := by
  have codeFits : start+size mode < 2^(8*mode.wordBytes) := by dsimp [beginPC,callPC,jumpPC] at fits;omega
  have init := Listing4StackInit.effect mode start state entry codeFits current
  have pc : (Listing4StackInit.finish mode start state).principal.pc = Arithmetic.encodeNat mode (jumpPC mode start) := by rw [init];rfl
  have targetFits : stptr mode start < 2^(8*mode.wordBytes) := by
    have bound := stptr_fits mode start codeFits;omega
  have effect := StackMemory.exchange_stack_effect mode (jumpPC mode start) (stptr mode start)
    (Listing4StackInit.finish mode start state).principal pc (first_reach mode start) targetFits
  change Execution.execute mode (exchange mode start) (Listing4StackInit.finish mode start state).principal = _ at effect
  rw [exchanged,StringStack.native_execute,effect,init,initial_stptr mode start state.principal.memory codeFits current]

theorem adjusted_effect (start : Nat) (state : StringExecution.State .x64)
    (entry : state.principal.pc = Arithmetic.encodeNat .x64 start)
    (fits : beginPC .x64 start < 2^64)
    (current : ByteMemory.bytesAt state.principal.memory start 34 = Listing4StackLayout.bytes .x64 start) :
    adjusted start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat .x64 (jumpPC .x64 start+7+8)
      accumulator := Arithmetic.encodeNat .x64 (stptr .x64 start)
      stack := Arithmetic.encodeNat .x64 (stptr .x64 start)
      carry := flag .x64 start state
      memory := ByteMemory.putWord .x64
        (ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start) state.principal.stack)
        (returnField .x64 start) (callTop .x64 start)}} := by
  have firstEffect := exchanged_effect .x64 start state entry fits current
  have pc : (exchanged .x64 start state).principal.pc = Arithmetic.encodeNat .x64 (jumpPC .x64 start+7) := by rw [firstEffect];rfl
  have targetFits : returnField .x64 start < 2^64 := by
    change returnField .x64 start<2^64
    dsimp [returnField]
    dsimp [beginPC,callPC,jumpPC,size,prefixSize] at fits
    omega
  have effect := WordAddImmediate.located_effect .x64 (jumpPC .x64 start+7) (returnField .x64 start) 18
    (exchanged .x64 start state).principal pc (fun _ => adjust_reach start) targetFits
  have read : MixedMemory.getWord .x64 (exchanged .x64 start state).principal.memory (returnField .x64 start) =
      Arithmetic.encodeNat .x64 (stptr .x64 start) := by
    rw [firstEffect,MixedFrames.word_after_word .x64 state.principal.memory (stptr .x64 start) (returnField .x64 start) _
      (Or.symm (fields_separate .x64 start))]
    exact initial_svptr start state.principal.memory (by dsimp [beginPC,callPC,jumpPC,size,prefixSize] at fits;omega) current
  rw [read,WordAddImmediate.positive_eighteen] at effect
  change WordAddImmediate.execute .x64
    (Relocation.memoryDisp .x64 (jumpPC .x64 start+7+8) (returnField .x64 start)) 18
    (exchanged .x64 start state).principal = _ at effect
  rw [adjusted,adjust,StringStack.execute,effect,firstEffect];rfl

theorem prefix_effect (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : beginPC mode start < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode) = Listing4StackLayout.bytes mode start) :
    prefixEnd mode start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (callPC mode start)
      accumulator := Listing4StackInit.accumulator mode start state
      stack := callTop mode start
      carry := flag mode start state
      memory := ByteMemory.putWord mode state.principal.memory (stptr mode start) state.principal.stack}} := by
  cases mode with
  | x86 => exact exchanged_effect .x86 start state entry fits current
  | x64 =>
    change beginPC .x64 start<2^64 at fits
    have previous := adjusted_effect start state entry fits current
    have pc : (adjusted start state).principal.pc = Arithmetic.encodeNat .x64 (jumpPC .x64 start+7+8) := by rw [previous]
    have targetFits : returnField .x64 start < 2^64 := by
      dsimp [returnField]
      dsimp [beginPC,callPC,jumpPC,size,prefixSize] at fits
      omega
    have effect := StackMemory.exchange_stack_effect .x64 (jumpPC .x64 start+7+8) (returnField .x64 start)
      (adjusted start state).principal pc (fun _ => saved_reach start) targetFits
    change Execution.execute .x64 (exchangeSaved start) (adjusted start state).principal = _ at effect
    have old : MixedMemory.getWord .x64 (ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start) state.principal.stack)
        (returnField .x64 start) = Arithmetic.encodeNat .x64 (stptr .x64 start) := by
      rw [MixedFrames.word_after_word .x64 _ _ _ _ (Or.symm (fields_separate .x64 start))]
      exact initial_svptr start state.principal.memory (by dsimp [beginPC,callPC,jumpPC,size,prefixSize] at fits;omega) current
    have back : ByteMemory.putWord .x64
        (ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start) state.principal.stack)
        (returnField .x64 start) (Arithmetic.encodeNat .x64 (stptr .x64 start)) =
        ByteMemory.putWord .x64 state.principal.memory (stptr .x64 start) state.principal.stack := by
      rw [←old,MixedMemory.put_get_back]
    have endpoint : jumpPC .x64 start+7+8+StackMemory.size .x64 = callPC .x64 start := by
      change jumpPC .x64 start+7+8+7=jumpPC .x64 start+22
      omega
    rw [prefixEnd,StringStack.native_execute,effect,previous]
    simp only [MixedMemory.get_put,Writes.put_word_overwrite,back,endpoint]
    rfl

theorem called_effect (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : beginPC mode start < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode) = Listing4StackLayout.bytes mode start) :
    finish mode start state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (beginPC mode start)
      accumulator := Listing4StackInit.accumulator mode start state
      stack := Arithmetic.encodeNat mode (returnField mode start)
      carry := flag mode start state
      memory := ByteMemory.putWord mode
        (ByteMemory.putWord mode state.principal.memory (stptr mode start) state.principal.stack)
        (returnField mode start) (Arithmetic.encodeNat mode (beginPC mode start))}} := by
  have previous := prefix_effect mode start state entry fits current
  have pc : (prefixEnd mode start state).principal.pc = Arithmetic.encodeNat mode (callPC mode start) := by rw [previous]
  have next := Relocation.next_pc mode (prefixEnd mode start state).principal (call mode) (callPC mode start) pc
  change Execution.nextPC mode (call mode) (prefixEnd mode start state).principal = Arithmetic.encodeNat mode (beginPC mode start) at next
  rw [call] at next
  have zero : Execution.displacementWord mode 0 = 0 := by cases mode <;> rfl
  have addZero : Arithmetic.encodeNat mode (beginPC mode start)+0 = Arithmetic.encodeNat mode (beginPC mode start) := by
    change (BitVec.ofNat (8*mode.wordBytes) (beginPC mode start))+0 = _
    exact BitVec.add_zero _
  have slotFits : returnField mode start < 2^(8*mode.wordBytes) := by
    cases mode <;> dsimp [returnField,beginPC,callPC,jumpPC,size,prefixSize] at * <;> omega
  rw [finish,StringStack.native_execute,call,Execution.execute,next,zero,addZero,Execution.callState,previous,
    stack_decrement,Arithmetic.encode_nat_toNat mode _ slotFits]
end SmcTuring.Appendix.Listing4JumpEffects
