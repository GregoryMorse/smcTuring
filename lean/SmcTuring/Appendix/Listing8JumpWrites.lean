module
public import SmcTuring.Appendix.Listing8JumpTrace
public import SmcTuring.Native.StringFieldWrites

public section
namespace SmcTuring.Appendix.Listing8JumpWrites
open Native Listing4StackLayout Listing8JumpLayout Listing8JumpEffects

theorem native_write (mode : Mode) (codeStart codeEnd : Nat) (form : Native.Form mode) (state : StringExecution.State mode)
    (owned : StringWrites.WordOwned mode codeStart codeEnd (Writes.address mode form state.principal)) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringStack.native mode form) state := by
  have lifted:=StringWrites.native_owned_run mode codeStart codeEnd [form] state ⟨owned,trivial⟩
  exact lifted.1

theorem exchange_write (mode : Mode) (codeStart codeEnd pc target : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+StackMemory.size mode) target)
    (owned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode target)) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringStack.native mode (StackMemory.form mode .exchangeStack pc target)) state := by
  have length : Native.instructionLength mode (.memory .exchangeStack 0)=StackMemory.size mode := by cases mode <;> rfl
  have hit:=Relocation.instruction_memory_hits mode .exchangeStack pc target state.principal entry (by simpa only [length] using range)
  apply native_write mode codeStart codeEnd _ state
  change StringWrites.WordOwned mode codeStart codeEnd
    (Execution.memoryAddress mode (Execution.nextPC mode (StackMemory.form mode .exchangeStack pc target) state.principal)
      (Relocation.instructionDisp mode .exchangeStack pc target))
  simp only [StackMemory.form]
  rw [hit]
  exact owned

theorem adjust_write (codeStart codeEnd origin : Nat) (state : StringExecution.State .x64)
    (entry : state.principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7))
    (owned : StringWrites.WordOwned .x64 codeStart codeEnd (Arithmetic.encodeNat .x64 (returnField .x64 origin))) :
    StringWrites.CodeWrite .x64 codeStart codeEnd (adjust origin) state := by
  have next : WordAddImmediate.next .x64 state.principal=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7+8) := by
    rw [WordAddImmediate.next,entry];exact BitVec.ofNat_add_ofNat _ _
  have hit : WordAddImmediate.address .x64
      (Relocation.memoryDisp .x64 (jumpPC .x64 origin+7+8) (returnField .x64 origin)) state.principal=
        Arithmetic.encodeNat .x64 (returnField .x64 origin) := by
    rw [WordAddImmediate.address,next]
    exact Relocation.memory_hits .x64 _ _ (fun _ => adjust_reach origin)
  have length : (StringWrites.packet .x64 (adjust origin) state).bytes.length=8 :=
    LittleEndian.word_encode_length _ _
  have address : (StringWrites.packet .x64 (adjust origin) state).address=
      (Arithmetic.encodeNat .x64 (returnField .x64 origin)).toNat := congrArg BitVec.toNat hit
  unfold StringWrites.CodeWrite
  rw [length,address]
  exact ⟨by decide,owned⟩

/-- Current stack declaration bytes derive the actual CALL stack pointer.
Both the temporary SP exchanges and the return-word store lie in code. -/
theorem owned (mode : Mode) (codeStart codeEnd origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (jumpPC mode origin))
    (capacity : failPC mode origin<2^(8*mode.wordBytes))
    (inside : codeStart≤origin ∧ origin+size mode≤codeEnd)
    (current : ByteMemory.bytesAt state.principal.memory origin (size mode)=Listing4StackLayout.bytes mode origin) :
    StringWrites.OwnedRun mode codeStart codeEnd (forms mode origin failed) state := by
  have stptrFits : stptr mode origin<2^(8*mode.wordBytes) := by
    have cap:=stack_capacity mode origin capacity
    have bound:=stptr_fits mode origin cap
    exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) bound) cap
  have savedFits : returnField mode origin<2^(8*mode.wordBytes) := by
    have cap:=stack_capacity mode origin capacity
    cases mode <;> simp [returnField,size,Mode.wordBytes] at cap ⊢ <;> omega
  have stptrOwned:=StringFieldWrites.word_owned mode codeStart codeEnd (stptr mode origin) stptrFits
    (by cases mode <;> simp [stptr,size,Mode.wordBytes] at inside ⊢ <;> omega)
  have savedOwned:=StringFieldWrites.word_owned mode codeStart codeEnd (returnField mode origin) savedFits
    (by cases mode <;> simp [returnField,size,Mode.wordBytes] at inside ⊢ <;> omega)
  have first:=exchange_write mode codeStart codeEnd (jumpPC mode origin) (stptr mode origin) state entry (first_reach mode origin) stptrOwned
  have called:=native_write mode codeStart codeEnd (call mode origin failed) (prefixEnd mode origin state) (by
    change StringWrites.WordOwned mode codeStart codeEnd ((prefixEnd mode origin state).principal.stack-Arithmetic.encodeNat mode mode.wordBytes)
    rw [prefix_effect mode origin state entry capacity current,Listing4JumpLayout.stack_decrement]
    exact savedOwned)
  cases mode with
  | x86 => exact ⟨first,called,trivial⟩
  | x64 =>
    have pc1 : (exchanged .x64 origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7) := by
      rw [exchanged_effect .x64 origin state entry capacity current];rfl
    have middle:=adjust_write codeStart codeEnd origin (exchanged .x64 origin state) pc1 savedOwned
    have pc2 : (adjusted origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7+8) := by
      rw [adjusted_effect origin state entry capacity current]
    have third:=exchange_write .x64 codeStart codeEnd (jumpPC .x64 origin+7+8) (returnField .x64 origin)
      (adjusted origin state) pc2 (fun _ => saved_reach origin) savedOwned
    exact ⟨first,middle,third,called,trivial⟩

end SmcTuring.Appendix.Listing8JumpWrites
