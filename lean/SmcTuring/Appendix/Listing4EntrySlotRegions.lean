module
public import SmcTuring.Appendix.Listing4TargetSlotRegions
public import SmcTuring.Appendix.Listing4StackWrites

public section
namespace SmcTuring.Appendix.Listing4EntrySlotRegions
open Native Listing4StackLayout

/-- Every initialization store is in the actual stptr operand. The x64
opcode gap and the separate return operand are outside that single word. -/
theorem initial_slots (mode : Mode) (origin : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode origin)
    (capacity : origin+size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory origin (size mode)=bytes mode origin) :
    StringStoreRegions.Run mode (Listing4StackTemplates.Slots mode origin) (forms mode origin) state := by
  have stFits : stptr mode origin<2^(8*mode.wordBytes) := by
    cases mode <;> simp [stptr,size,Mode.wordBytes] at capacity ⊢ <;> omega
  have owned:=StringFieldWrites.word_owned mode (stptr mode origin) (stptr mode origin+mode.wordBytes)
    (stptr mode origin) stFits ⟨Nat.le_refl _,Nat.le_refl _⟩
  apply BoundedStoreRegions.interval mode _ (stptr mode origin) (stptr mode origin+mode.wordBytes) _ state
    (fun _ _ lower upper => Or.inl ⟨lower,upper⟩)
  cases mode with
  | x86 =>
    exact StringInitWrites.owned .x86 (stptr .x86 origin) (stptr .x86 origin+4) origin (stptr .x86 origin) state entry capacity
      (by simp [stptr,size,Mode.wordBytes] at capacity ⊢;omega)
      (by simp [StringInit.field,StringCodec.fieldOffset,stptr,Mode.wordBytes]) ⟨Nat.le_refl _,Nat.le_refl _⟩ current
  | x64 =>
    have first:=StackFieldWrites.memory .x64 .exchangeAcc (by decide) (stptr .x64 origin) (stptr .x64 origin+8)
      origin (stptr .x64 origin) state entry
      (by intro _;change Relocation.SignedDelta (origin+7) (origin+16);unfold Relocation.SignedDelta Relocation.delta;omega) owned
    have pc1 : (Listing4StackInit.swapped origin state).principal.pc=Arithmetic.encodeNat .x64 (origin+7) := by
      rw [Listing4StackInit.swapped_effect origin state entry capacity current]
    have second:=StackFieldWrites.memory .x64 .storeAcc (by decide) (stptr .x64 origin) (stptr .x64 origin+8)
      (origin+7) (stptr .x64 origin) (Listing4StackInit.swapped origin state) pc1
      (by intro _;change Relocation.SignedDelta (origin+7+7) (origin+16);unfold Relocation.SignedDelta Relocation.delta;omega) owned
    have third:=Listing8JumpWrites.native_write .x64 (stptr .x64 origin) (stptr .x64 origin+8)
      (Listing4StackLayout.third origin) (Listing4StackInit.restored origin state) owned
    have fourth:=Listing8JumpWrites.native_write .x64 (stptr .x64 origin) (stptr .x64 origin+8)
      (Listing4StackLayout.fourth origin) (Listing4StackInit.stored origin state) owned
    exact ⟨first,second,third,fourth,trivial⟩

/-- The original early CALL prefix has exactly the same two slot owners as
the later CALL. Its actual stack destination is derived from initialized bytes. -/
theorem jump (mode : Mode) (origin : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode origin)
    (capacity : Listing4JumpLayout.beginPC mode origin<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory origin (size mode)=bytes mode origin) :
    StringStoreRegions.Run mode (Listing4StackTemplates.Slots mode origin) (Listing4JumpLayout.forms mode origin)
      (Listing4StackInit.finish mode origin state) := by
  have stackFits : origin+size mode<2^(8*mode.wordBytes) := by
    dsimp [Listing4JumpLayout.beginPC,Listing4JumpLayout.callPC,Listing4JumpLayout.jumpPC] at capacity;omega
  have stFits : stptr mode origin<2^(8*mode.wordBytes) := by
    cases mode <;> simp [stptr,size,Mode.wordBytes] at stackFits ⊢ <;> omega
  have retFits : returnField mode origin<2^(8*mode.wordBytes) := by
    cases mode <;> simp [returnField,size,Mode.wordBytes] at stackFits ⊢ <;> omega
  have stOwned:=StringFieldWrites.word_owned mode (stptr mode origin) (stptr mode origin+mode.wordBytes) _ stFits ⟨Nat.le_refl _,Nat.le_refl _⟩
  have retOwned:=StringFieldWrites.word_owned mode (returnField mode origin) (returnField mode origin+mode.wordBytes) _ retFits ⟨Nat.le_refl _,Nat.le_refl _⟩
  have pc : (Listing4StackInit.finish mode origin state).principal.pc=Arithmetic.encodeNat mode (Listing4JumpLayout.jumpPC mode origin) := by
    rw [Listing4StackInit.effect mode origin state entry stackFits current];rfl
  have first:=Listing8JumpWrites.exchange_write mode (stptr mode origin) (stptr mode origin+mode.wordBytes)
    (Listing4JumpLayout.jumpPC mode origin) (stptr mode origin) (Listing4StackInit.finish mode origin state) pc
    (Listing4JumpLayout.first_reach mode origin) stOwned
  have called:=Listing8JumpWrites.native_write mode (returnField mode origin) (returnField mode origin+mode.wordBytes)
    (Listing4JumpLayout.call mode) (Listing4JumpEffects.prefixEnd mode origin state) (by
      change StringWrites.WordOwned mode _ _ ((Listing4JumpEffects.prefixEnd mode origin state).principal.stack-Arithmetic.encodeNat mode mode.wordBytes)
      rw [Listing4JumpEffects.prefix_effect mode origin state entry capacity current,Listing4JumpLayout.stack_decrement]
      exact retOwned)
  have firstRegion:=Listing4TargetSlotRegions.at_field mode origin _ _ _ first (BoundedStoreRegions.native_length mode _ _) (Or.inl rfl)
  have callRegion:=Listing4TargetSlotRegions.at_field mode origin _ _ _ called (BoundedStoreRegions.native_length mode _ _) (Or.inr rfl)
  cases mode with
  | x86 => exact ⟨firstRegion,callRegion,trivial⟩
  | x64 =>
    have pc1 : (Listing4JumpEffects.exchanged .x64 origin state).principal.pc=Arithmetic.encodeNat .x64 (Listing4JumpLayout.jumpPC .x64 origin+7) := by
      rw [Listing4JumpEffects.exchanged_effect .x64 origin state entry capacity current];rfl
    have middle:=StackFieldWrites.add .x64 (returnField .x64 origin) (returnField .x64 origin+8)
      (Listing4JumpLayout.jumpPC .x64 origin+7) (returnField .x64 origin) 18
      (Listing4JumpEffects.exchanged .x64 origin state) pc1 (fun _ => Listing4JumpLayout.adjust_reach origin) retOwned
    have pc2 : (Listing4JumpEffects.adjusted origin state).principal.pc=Arithmetic.encodeNat .x64 (Listing4JumpLayout.jumpPC .x64 origin+7+8) := by
      rw [Listing4JumpEffects.adjusted_effect origin state entry capacity current]
    have third:=Listing8JumpWrites.exchange_write .x64 (returnField .x64 origin) (returnField .x64 origin+8)
      (Listing4JumpLayout.jumpPC .x64 origin+7+8) (returnField .x64 origin) (Listing4JumpEffects.adjusted origin state) pc2
      (fun _ => Listing4JumpLayout.saved_reach origin) retOwned
    exact ⟨firstRegion,
      Listing4TargetSlotRegions.at_field .x64 origin _ _ _ middle (LittleEndian.word_encode_length _ _) (Or.inr rfl),
      Listing4TargetSlotRegions.at_field .x64 origin _ _ _ third (BoundedStoreRegions.native_length .x64 _ _) (Or.inr rfl),callRegion,trivial⟩

/-- All eight/thirteen original bootstrap instructions store only in the two
complete stack operands, with the intervening opcode gap protected. -/
theorem entry (mode : Mode) (origin : Nat) (seed : StringExecution.State mode)
    (capacity : Listing4EntryLayout.mainPC mode origin<2^(8*mode.wordBytes)) :
    StringStoreRegions.Run mode (Listing4StackTemplates.Slots mode origin) (Listing4EntryLayout.forms mode origin)
      (Listing4Entry.initial mode origin seed) := by
  have current : ByteMemory.bytesAt (Listing4Entry.initial mode origin seed).principal.memory origin (size mode)=bytes mode origin :=
    Listing4Entry.stack_current mode origin seed
  have first:=initial_slots mode origin (Listing4Entry.initial mode origin seed) rfl
    (Listing4EntryLayout.stack_capacity mode origin capacity) current
  have second:=jump mode origin (Listing4Entry.initial mode origin seed) rfl
    (by rw [Listing4Boot.endpoint];exact Listing4EntryLayout.boot_capacity mode origin capacity) current
  have last:=Listing4TargetSlotRegions.regions mode origin (Listing4JumpLayout.beginPC mode origin)
    (Arithmetic.encodeNat mode (Listing4JumpLayout.beginPC mode origin)) (Listing4Entry.targetSeed mode origin seed)
    (Listing4EntryLayout.begin_ranges mode origin) (Listing4EntryLayout.stack_capacity mode origin capacity) current
  rw [←Listing4Entry.call_shape mode origin seed capacity] at last
  have initRun:=Listing4StackWrites.initialize_run mode origin (Listing4Entry.initial mode origin seed) rfl
    (Listing4EntryLayout.stack_capacity mode origin capacity) current
  have bootRun : StringWrites.run mode (forms mode origin++Listing4JumpLayout.forms mode origin)
      (Listing4Entry.initial mode origin seed)=Listing4Entry.beforeTarget mode origin seed :=
    StringWrites.trace_run_eq mode (Listing4Boot.trace mode origin (Listing4Entry.initial mode origin seed) rfl
      (Listing4EntryLayout.boot_capacity mode origin capacity) (Listing4Entry.boot_current mode origin seed))
  rw [Listing4EntryLayout.forms,StringStoreRegions.append,Listing4Boot.forms,StringStoreRegions.append,initRun,bootRun]
  exact ⟨⟨first,second⟩,last⟩

end SmcTuring.Appendix.Listing4EntrySlotRegions
