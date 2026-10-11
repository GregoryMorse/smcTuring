module
public import SmcTuring.Native.StackFieldWrites
public import SmcTuring.Native.StringInitWrites
public import SmcTuring.Appendix.Listing4Entry

public section
namespace SmcTuring.Appendix.Listing4StackWrites
open Native Listing4StackLayout

theorem slots (mode : Mode) (codeStart codeEnd start : Nat)
    (capacity : start+size mode<2^(8*mode.wordBytes))
    (inside : codeStart≤start ∧ start+size mode≤codeEnd) :
    StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (stptr mode start)) ∧
    StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (returnField mode start)) := by
  constructor
  · apply StringFieldWrites.word_owned mode codeStart codeEnd _
    · have bound:=stptr_fits mode start capacity;exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) bound) capacity
    · cases mode <;> simp [stptr,size,Mode.wordBytes] at inside ⊢ <;> omega
  · apply StringFieldWrites.word_owned mode codeStart codeEnd _
    · cases mode <;> simp [returnField,size,Mode.wordBytes] at capacity ⊢ <;> omega
    · cases mode <;> simp [returnField,size,Mode.wordBytes] at inside ⊢ <;> omega

theorem initialize_owned (mode : Mode) (codeStart codeEnd start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (capacity : start+size mode<2^(8*mode.wordBytes))
    (inside : codeStart≤start ∧ start+size mode≤codeEnd)
    (current : ByteMemory.bytesAt state.principal.memory start (size mode)=bytes mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd (forms mode start) state := by
  have owned:=(slots mode codeStart codeEnd start capacity inside).1
  cases mode with
  | x86 =>
    have result:=StringInitWrites.owned .x86 codeStart codeEnd start (stptr .x86 start) state entry capacity
      (by simp [stptr,size,Mode.wordBytes] at capacity ⊢;omega)
      (by simp [StringInit.field,StringCodec.fieldOffset,size,Mode.wordBytes] at inside ⊢;omega)
      (by simp [stptr,size,Mode.wordBytes] at inside ⊢;omega) current
    exact result
  | x64 =>
    have first:=StackFieldWrites.memory .x64 .exchangeAcc (by decide) codeStart codeEnd start (stptr .x64 start) state entry
      (by intro _;change Relocation.SignedDelta (start+7) (start+16);unfold Relocation.SignedDelta Relocation.delta;omega) owned
    have pc1 : (Listing4StackInit.swapped start state).principal.pc=Arithmetic.encodeNat .x64 (start+7) := by
      rw [Listing4StackInit.swapped_effect start state entry capacity current]
    have second:=StackFieldWrites.memory .x64 .storeAcc (by decide) codeStart codeEnd (start+7) (stptr .x64 start)
      (Listing4StackInit.swapped start state) pc1
      (by intro _;change Relocation.SignedDelta (start+7+7) (start+16);unfold Relocation.SignedDelta Relocation.delta;omega) owned
    have third:=Listing8JumpWrites.native_write .x64 codeStart codeEnd (Listing4StackLayout.third start)
      (Listing4StackInit.restored start state) owned
    have fourth:=Listing8JumpWrites.native_write .x64 codeStart codeEnd (Listing4StackLayout.fourth start)
      (Listing4StackInit.stored start state) owned
    exact ⟨first,second,third,fourth,trivial⟩

theorem initialize_run (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (capacity : start+size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode)=bytes mode start) :
    StringWrites.run mode (forms mode start) state=Listing4StackInit.finish mode start state :=
  StringWrites.trace_run_eq mode (Listing4StackInitTrace.trace mode start state entry capacity current)

theorem jump_owned (mode : Mode) (codeStart codeEnd start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (capacity : Listing4JumpLayout.beginPC mode start<2^(8*mode.wordBytes))
    (inside : codeStart≤start ∧ start+size mode≤codeEnd)
    (current : ByteMemory.bytesAt state.principal.memory start (size mode)=bytes mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd (Listing4JumpLayout.forms mode start) (Listing4StackInit.finish mode start state) := by
  have stackFits : start+size mode<2^(8*mode.wordBytes) := by
    dsimp [Listing4JumpLayout.beginPC,Listing4JumpLayout.callPC,Listing4JumpLayout.jumpPC] at capacity;omega
  have ⟨stptrOwned,savedOwned⟩:=slots mode codeStart codeEnd start stackFits inside
  have pc : (Listing4StackInit.finish mode start state).principal.pc=Arithmetic.encodeNat mode (Listing4JumpLayout.jumpPC mode start) := by
    rw [Listing4StackInit.effect mode start state entry stackFits current];rfl
  have first:=Listing8JumpWrites.exchange_write mode codeStart codeEnd (Listing4JumpLayout.jumpPC mode start) (stptr mode start)
    (Listing4StackInit.finish mode start state) pc (Listing4JumpLayout.first_reach mode start) stptrOwned
  have called:=Listing8JumpWrites.native_write mode codeStart codeEnd (Listing4JumpLayout.call mode)
    (Listing4JumpEffects.prefixEnd mode start state) (by
      change StringWrites.WordOwned mode codeStart codeEnd ((Listing4JumpEffects.prefixEnd mode start state).principal.stack-Arithmetic.encodeNat mode mode.wordBytes)
      rw [Listing4JumpEffects.prefix_effect mode start state entry capacity current,Listing4JumpLayout.stack_decrement]
      exact savedOwned)
  cases mode with
  | x86 => exact ⟨first,called,trivial⟩
  | x64 =>
    have pc1 : (Listing4JumpEffects.exchanged .x64 start state).principal.pc=Arithmetic.encodeNat .x64 (Listing4JumpLayout.jumpPC .x64 start+7) := by
      rw [Listing4JumpEffects.exchanged_effect .x64 start state entry capacity current];rfl
    have middle:=StackFieldWrites.add .x64 codeStart codeEnd (Listing4JumpLayout.jumpPC .x64 start+7) (returnField .x64 start) 18
      (Listing4JumpEffects.exchanged .x64 start state) pc1 (fun _ => Listing4JumpLayout.adjust_reach start) savedOwned
    have pc2 : (Listing4JumpEffects.adjusted start state).principal.pc=Arithmetic.encodeNat .x64 (Listing4JumpLayout.jumpPC .x64 start+7+8) := by
      rw [Listing4JumpEffects.adjusted_effect start state entry capacity current]
    have third:=Listing8JumpWrites.exchange_write .x64 codeStart codeEnd (Listing4JumpLayout.jumpPC .x64 start+7+8) (returnField .x64 start)
      (Listing4JumpEffects.adjusted start state) pc2 (fun _ => Listing4JumpLayout.saved_reach start) savedOwned
    exact ⟨first,middle,third,called,trivial⟩

theorem boot_owned (mode : Mode) (codeStart codeEnd start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (capacity : start+Listing4Boot.size mode<2^(8*mode.wordBytes))
    (inside : codeStart≤start ∧ start+size mode≤codeEnd)
    (current : ByteMemory.bytesAt state.principal.memory start (Listing4Boot.size mode)=Listing4Boot.bytes mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd (Listing4Boot.forms mode start) state := by
  have stackCurrent:=Listing4Boot.stack_packet mode start state.principal.memory current
  have stackFits : start+size mode<2^(8*mode.wordBytes) := by
    cases mode <;> dsimp [size,Listing4Boot.size] at capacity ⊢ <;> omega
  rw [Listing4Boot.forms,StringWrites.owned_run_append,initialize_run mode start state entry stackFits stackCurrent]
  exact ⟨initialize_owned mode codeStart codeEnd start state entry stackFits inside stackCurrent,
    jump_owned mode codeStart codeEnd start state entry (by rw [Listing4Boot.endpoint];exact capacity) inside stackCurrent⟩

end SmcTuring.Appendix.Listing4StackWrites
