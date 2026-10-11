module
public import SmcTuring.Appendix.Listing4TargetMemory

public section
namespace SmcTuring.Appendix.Listing4TargetEffects
open Native Listing4StackLayout Listing4TargetLayout
/-- Explicit CALL result shape. The complete bootstrap theorem below derives
this shape from the executed CALL; it is not a future readiness assumption. -/
@[expose] def entry (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode) :=
  {seed with principal := {seed.principal with
    pc := Arithmetic.encodeNat mode target
    stack := Arithmetic.encodeNat mode (returnField mode start)
    memory := ByteMemory.putWord mode
      (ByteMemory.putWord mode seed.principal.memory (returnField mode start) ret)
      (stptr mode start) seed.principal.stack}}
@[expose] def swapped (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (first mode start target)) (entry mode start target ret seed)
@[expose] def adjusted (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode) :=
  StringStack.execute mode (adjust mode start target) (swapped mode start target ret seed)
@[expose] def exchanged (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (third mode start target)) (adjusted mode start target ret seed)
@[expose] def stored (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (fourth mode start target)) (exchanged mode start target ret seed)
@[expose] def finish (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode) :=
  StringStack.execute mode (StringStack.native mode (fifth mode start target)) (stored mode start target ret seed)
@[expose] def flag (mode : Mode) (start : Nat) : Bool :=
  match mode with
  | .x86 => BitVec.uaddOverflow (Arithmetic.encodeNat .x86 (returnField .x86 start)) (Arithmetic.encodeNat .x86 4)
  | .x64 => Arithmetic.unsignedBorrow (Arithmetic.encodeNat .x64 (returnField .x64 start)) (Arithmetic.encodeNat .x64 10)

theorem swapped_effect (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes)) :
    swapped mode start target ret seed = {seed with principal := {seed.principal with
      pc := Arithmetic.encodeNat mode (target+StackMemory.size mode)
      memory := ByteMemory.putWord mode (ByteMemory.putWord mode seed.principal.memory (returnField mode start) ret)
        (stptr mode start) (Arithmetic.encodeNat mode (returnField mode start))}} := by
  have fieldFits : stptr mode start<2^(8*mode.wordBytes) := by have h:=stptr_fits mode start fits;omega
  have effect := StackMemory.exchange_stack_effect mode target (stptr mode start) (entry mode start target ret seed).principal rfl ranges.first fieldFits
  change Execution.execute mode (first mode start target) (entry mode start target ret seed).principal=_ at effect
  rw [swapped,StringStack.native_execute,effect,entry,MixedMemory.get_put,Writes.put_word_overwrite]

theorem adjusted_effect (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes)) :
    adjusted mode start target ret seed = {seed with principal := {seed.principal with
      pc := Arithmetic.encodeNat mode (thirdPC mode target)
      carry := flag mode start
      memory := ByteMemory.putWord mode (ByteMemory.putWord mode seed.principal.memory (returnField mode start) ret)
        (stptr mode start) (Arithmetic.encodeNat mode (stptr mode start))}} := by
  have previous := swapped_effect mode start target ret seed ranges fits
  have fieldFits : stptr mode start<2^(8*mode.wordBytes) := by have h:=stptr_fits mode start fits;omega
  cases mode with
  | x86 =>
    have pc : (swapped .x86 start target ret seed).principal.pc=Arithmetic.encodeNat .x86 (target+6) := by rw [previous];rfl
    have effect := WordAddImmediate.located_effect .x86 (target+6) (stptr .x86 start) 4
      (swapped .x86 start target ret seed).principal pc (by intro impossible;cases impossible) fieldFits
    have read : MixedMemory.getWord .x86 (swapped .x86 start target ret seed).principal.memory (stptr .x86 start)=
        Arithmetic.encodeNat .x86 (returnField .x86 start) := by rw [previous,MixedMemory.get_put]
    rw [read,WordAddImmediate.positive_four] at effect
    change WordAddImmediate.execute .x86 (Relocation.memoryDisp .x86 (target+6+7) (stptr .x86 start)) 4
      (swapped .x86 start target ret seed).principal=_ at effect
    rw [adjusted,adjust,StringStack.execute,effect,previous]
    simp only [Writes.put_word_overwrite,slot_adjustment .x86 start]
    rfl
  | x64 =>
    have pc : (swapped .x64 start target ret seed).principal.pc=Arithmetic.encodeNat .x64 (target+7) := by rw [previous];rfl
    have adjustRange : Mode.x64=Mode.x64 → Relocation.SignedDelta (target+7+8) (stptr .x64 start) := ranges.adjust
    have effect := StackAdjust.subtract_effect .x64 (target+7) (stptr .x64 start) 10 (swapped .x64 start target ret seed) pc
      (by simpa only [show StringCodec.subSize .x64 10=8 from rfl] using adjustRange) (by decide) fieldFits
    have read : MixedMemory.getWord .x64 (swapped .x64 start target ret seed).principal.memory (stptr .x64 start)=
        Arithmetic.encodeNat .x64 (returnField .x64 start) := by rw [previous,MixedMemory.get_put]
    rw [read] at effect
    rw [adjusted,adjust,effect,previous]
    simp only [Writes.put_word_overwrite,slot_adjustment .x64 start]
    rfl

theorem exchanged_effect (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes)) :
    exchanged mode start target ret seed = {seed with principal := {seed.principal with
      pc := Arithmetic.encodeNat mode (fourthPC mode target)
      accumulator := Arithmetic.encodeNat mode (stptr mode start)
      carry := flag mode start
      memory := ByteMemory.putWord mode (ByteMemory.putWord mode seed.principal.memory (returnField mode start) ret)
        (stptr mode start) seed.principal.accumulator}} := by
  have previous := adjusted_effect mode start target ret seed ranges fits
  have pc : (adjusted mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (thirdPC mode target) := by rw [previous]
  have fieldFits : stptr mode start<2^(8*mode.wordBytes) := by have h:=stptr_fits mode start fits;omega
  have effect := WordMemoryArithmetic.located_effect mode .exchange (thirdPC mode target) (stptr mode start)
    (adjusted mode start target ret seed).principal pc ranges.third fieldFits
  change Execution.execute mode (third mode start target) (adjusted mode start target ret seed).principal=_ at effect
  rw [exchanged,StringStack.native_execute,effect,previous]
  simp only [MixedMemory.get_put,Writes.put_word_overwrite]
  rfl

theorem stored_effect (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt seed.principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start) :
    stored mode start target ret seed = {seed with principal := {seed.principal with
      pc := Arithmetic.encodeNat mode (fifthPC mode target)
      accumulator := Arithmetic.encodeNat mode (stptr mode start)
      carry := flag mode start
      memory := ByteMemory.putWord mode seed.principal.memory (stptr mode start) seed.principal.accumulator}} := by
  have previous := exchanged_effect mode start target ret seed ranges fits
  have pc : (exchanged mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fourthPC mode target) := by rw [previous]
  have fieldFits : returnField mode start<2^(8*mode.wordBytes) := by
    cases mode <;> dsimp [returnField,Listing4StackLayout.size,Mode.wordBytes] at * <;> omega
  have effect := StackMemory.store_acc_effect mode (fourthPC mode target) (returnField mode start)
    (exchanged mode start target ret seed).principal pc ranges.fourth fieldFits
  change Execution.execute mode (fourth mode start target) (exchanged mode start target ret seed).principal=_ at effect
  rw [stored,StringStack.native_execute,effect,previous,Listing4TargetMemory.restore_return mode start seed.principal.memory ret seed.principal.accumulator fits current]
  rfl

theorem effect (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt seed.principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start) :
    finish mode start target ret seed = {seed with principal := {seed.principal with
      pc := Arithmetic.encodeNat mode (endPC mode target)
      carry := flag mode start}} := by
  have previous := stored_effect mode start target ret seed ranges fits current
  have pc : (stored mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fifthPC mode target) := by rw [previous]
  have fieldFits : stptr mode start<2^(8*mode.wordBytes) := by have h:=stptr_fits mode start fits;omega
  have last := WordMemoryArithmetic.located_effect mode .exchange (fifthPC mode target) (stptr mode start)
    (stored mode start target ret seed).principal pc ranges.fifth fieldFits
  change Execution.execute mode (fifth mode start target) (stored mode start target ret seed).principal=_ at last
  have back : ByteMemory.putWord mode seed.principal.memory (stptr mode start) (Arithmetic.encodeNat mode (stptr mode start))=seed.principal.memory := by
    rw [←initial_stptr mode start seed.principal.memory fits current,MixedMemory.put_get_back]
  rw [finish,StringStack.native_execute,last,previous]
  simp only [MixedMemory.get_put,WordMemoryArithmetic.accumulator,WordMemoryArithmetic.flag,WordMemoryArithmetic.result,Writes.put_word_overwrite,back]
  rfl
end SmcTuring.Appendix.Listing4TargetEffects
