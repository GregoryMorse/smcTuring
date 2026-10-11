module
public import SmcTuring.Appendix.Listing8JumpLayout

public section
namespace SmcTuring.Appendix.Listing8JumpEffects
open Native LittleEndian Listing4StackLayout Listing8JumpLayout
@[expose] def exchanged (mode : Mode) (origin : Nat) (state : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (exchange mode origin)) state
@[expose] def adjusted (origin : Nat) (state : StringExecution.State .x64) :=
  StringStack.execute .x64 (adjust origin) (exchanged .x64 origin state)
@[expose] def prefixEnd (mode : Mode) (origin : Nat) (state : StringExecution.State mode) : StringExecution.State mode :=
  match mode with
  | .x86 => exchanged .x86 origin state
  | .x64 => StringStack.execute .x64 (StringStack.native .x64 (exchangeSaved origin)) (adjusted origin state)
@[expose] def finish (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (call mode origin failed)) (prefixEnd mode origin state)

theorem exchanged_effect (mode : Mode) (origin : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (jumpPC mode origin))
    (capacity : failPC mode origin<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory origin (size mode)=Listing4StackLayout.bytes mode origin) :
    exchanged mode origin state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (jumpPC mode origin+StackMemory.size mode)
      stack:=Arithmetic.encodeNat mode (stptr mode origin)
      memory:=ByteMemory.putWord mode state.principal.memory (stptr mode origin) state.principal.stack}} := by
  have fits:=stack_capacity mode origin capacity
  have bound:=stptr_fits mode origin fits
  have targetFits : stptr mode origin<2^(8*mode.wordBytes) := by omega
  have effect:=StackMemory.exchange_stack_effect mode (jumpPC mode origin) (stptr mode origin) state.principal entry
    (first_reach mode origin) targetFits
  change Execution.execute mode (exchange mode origin) state.principal=_ at effect
  rw [exchanged,StringStack.native_execute,effect,initial_stptr mode origin state.principal.memory fits current]

theorem adjusted_effect (origin : Nat) (state : StringExecution.State .x64)
    (entry : state.principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin))
    (capacity : failPC .x64 origin<2^64)
    (current : ByteMemory.bytesAt state.principal.memory origin 34=Listing4StackLayout.bytes .x64 origin) :
    adjusted origin state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7+8)
      stack:=Arithmetic.encodeNat .x64 (stptr .x64 origin)
      carry:=Listing4JumpEffects.flag .x64 origin state
      memory:=ByteMemory.putWord .x64
        (ByteMemory.putWord .x64 state.principal.memory (stptr .x64 origin) state.principal.stack)
        (returnField .x64 origin) (Listing4JumpLayout.callTop .x64 origin)}} := by
  have first:=exchanged_effect .x64 origin state entry capacity current
  have pc : (exchanged .x64 origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7) := by rw [first];rfl
  have fits : origin+34<2^64 := stack_capacity .x64 origin capacity
  have targetFits : returnField .x64 origin<2^64 := by dsimp [returnField,size] at *;omega
  have effect:=WordAddImmediate.located_effect .x64 (jumpPC .x64 origin+7) (returnField .x64 origin) 18
    (exchanged .x64 origin state).principal pc (fun _ => adjust_reach origin) targetFits
  have read : MixedMemory.getWord .x64 (exchanged .x64 origin state).principal.memory (returnField .x64 origin)=
      Arithmetic.encodeNat .x64 (stptr .x64 origin) := by
    rw [first,MixedFrames.word_after_word .x64 _ _ _ _ (Or.symm (fields_separate .x64 origin))]
    exact initial_svptr origin state.principal.memory fits current
  rw [read,WordAddImmediate.positive_eighteen] at effect
  change WordAddImmediate.execute .x64
    (Relocation.memoryDisp .x64 (jumpPC .x64 origin+7+8) (returnField .x64 origin)) 18
    (exchanged .x64 origin state).principal=_ at effect
  rw [adjusted,adjust,StringStack.execute,effect,first];rfl

theorem prefix_effect (mode : Mode) (origin : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (jumpPC mode origin))
    (capacity : failPC mode origin<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory origin (size mode)=Listing4StackLayout.bytes mode origin) :
    prefixEnd mode origin state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (callPC mode origin)
      stack:=Listing4JumpLayout.callTop mode origin
      carry:=Listing4JumpEffects.flag mode origin state
      memory:=ByteMemory.putWord mode state.principal.memory (stptr mode origin) state.principal.stack}} := by
  cases mode with
  | x86 => exact exchanged_effect .x86 origin state entry capacity current
  | x64 =>
    change failPC .x64 origin<2^64 at capacity
    have previous:=adjusted_effect origin state entry capacity current
    have pc : (adjusted origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7+8) := by rw [previous]
    have fits : origin+34<2^64 := stack_capacity .x64 origin capacity
    have targetFits : returnField .x64 origin<2^64 := by dsimp [returnField,size] at *;omega
    have effect:=StackMemory.exchange_stack_effect .x64 (jumpPC .x64 origin+7+8) (returnField .x64 origin)
      (adjusted origin state).principal pc (fun _ => saved_reach origin) targetFits
    change Execution.execute .x64 (exchangeSaved origin) (adjusted origin state).principal=_ at effect
    have old : MixedMemory.getWord .x64 (ByteMemory.putWord .x64 state.principal.memory (stptr .x64 origin) state.principal.stack)
        (returnField .x64 origin)=Arithmetic.encodeNat .x64 (stptr .x64 origin) := by
      rw [MixedFrames.word_after_word .x64 _ _ _ _ (Or.symm (fields_separate .x64 origin))]
      exact initial_svptr origin state.principal.memory fits current
    have back : ByteMemory.putWord .x64
        (ByteMemory.putWord .x64 state.principal.memory (stptr .x64 origin) state.principal.stack)
        (returnField .x64 origin) (Arithmetic.encodeNat .x64 (stptr .x64 origin))=
        ByteMemory.putWord .x64 state.principal.memory (stptr .x64 origin) state.principal.stack := by
      rw [←old,MixedMemory.put_get_back]
    have endpoint : jumpPC .x64 origin+7+8+StackMemory.size .x64=callPC .x64 origin := by
      change jumpPC .x64 origin+7+8+7=jumpPC .x64 origin+22;omega
    rw [prefixEnd,StringStack.native_execute,effect,previous]
    simp only [MixedMemory.get_put,Writes.put_word_overwrite,back,endpoint]

theorem called_effect (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (jumpPC mode origin))
    (capacity : failPC mode origin<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory origin (size mode)=Listing4StackLayout.bytes mode origin) :
    finish mode origin failed state={state with principal:={state.principal with
      pc:=(if failed then Arithmetic.encodeNat mode (failPC mode origin) else Arithmetic.encodeNat mode (Listing8BootImage.beginPC mode origin))
      stack:=Arithmetic.encodeNat mode (returnField mode origin)
      carry:=Listing4JumpEffects.flag mode origin state
      memory:=ByteMemory.putWord mode
        (ByteMemory.putWord mode state.principal.memory (stptr mode origin) state.principal.stack)
        (returnField mode origin) (Arithmetic.encodeNat mode (failPC mode origin))}} := by
  have previous:=prefix_effect mode origin state entry capacity current
  have pc : (prefixEnd mode origin state).principal.pc=Arithmetic.encodeNat mode (callPC mode origin) := by rw [previous]
  have next:=Relocation.next_pc mode (prefixEnd mode origin state).principal (call mode origin failed) (callPC mode origin) pc
  change Execution.nextPC mode (call mode origin failed) (prefixEnd mode origin state).principal=Arithmetic.encodeNat mode (failPC mode origin) at next
  have hit:=Listing8CallSelection.call_target mode (callPC mode origin) (Listing8BootImage.beginPC mode origin) failed
    (prefixEnd mode origin state).principal pc (backedge_reach mode origin)
  rw [Listing8CallSelection.displacement_selection] at hit
  change Execution.nextPC mode (call mode origin failed) (prefixEnd mode origin state).principal+
    Execution.displacementWord mode (if failed then 0 else Relocation.relative32 (failPC mode origin) (Listing8BootImage.beginPC mode origin))=
      (if failed then Arithmetic.encodeNat mode (failPC mode origin) else Arithmetic.encodeNat mode (Listing8BootImage.beginPC mode origin)) at hit
  have fits:=stack_capacity mode origin capacity
  have slotFits : returnField mode origin<2^(8*mode.wordBytes) := by
    cases mode <;> dsimp [returnField,size] at fits ⊢ <;> omega
  dsimp only [call] at hit next
  rw [finish,StringStack.native_execute,call,Execution.execute,hit,next,Execution.callState,previous,
    Listing4JumpLayout.stack_decrement,Arithmetic.encode_nat_toNat mode _ slotFits]
end SmcTuring.Appendix.Listing8JumpEffects
