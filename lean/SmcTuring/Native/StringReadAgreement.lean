module
public import SmcTuring.Native.StringReadWindows

public section
namespace SmcTuring.Native.StringReadAgreement
open MemoryRegion StringReadWindows

@[expose] def AgreeState (mode : Mode) (region : Region)
    (left right : StringExecution.State mode) : Prop :=
  RegionExecution.StateAgree mode region left.principal right.principal ∧
    left.sourceIndex=right.sourceIndex ∧ left.destinationIndex=right.destinationIndex ∧ left.backwards=right.backwards

theorem dword_agree (region : Region) {left right : ByteMemory.Memory} (same : Agree region left right)
    (address : Nat) (inside : region.Contains address 4) : DwordCode.get left address=DwordCode.get right address := by
  unfold DwordCode.get
  rw [bytes_agree region same address 4 inside]

theorem native_within (mode : Mode) (region : Region) (form : Native.Form mode) (state : Execution.State mode)
    (contained : Contained region (native mode form state)) : RegionExecution.ReadWithin mode region form state := by
  unfold native Contained at contained
  unfold RegionExecution.ReadWithin
  cases current : RegionExecution.readAddress mode form state with
  | none => trivial
  | some address => simpa only [current,Option.map_some] using contained

/-- The string-form effects depend only on the declared data-read window,
the represented registers and loaded bytes. Exterior memory is arbitrary. -/
theorem string_agrees (mode : Mode) (region : Region) (form : StringForm.Form mode)
    (left right : StringExecution.State mode) (same : AgreeState mode region left right)
    (contained : Contained region (string mode form right)) :
    AgreeState mode region (StringExecution.execute mode form left) (StringExecution.execute mode form right) := by
  cases form with
  | native form => exact ⟨RegionExecution.execute_agrees mode region form left.principal right.principal same.1
      (native_within mode region form right.principal contained),same.2⟩
  | initialize32 address value =>
    exact ⟨⟨by simp only [StringExecution.execute,StringExecution.nextPC,same.1.1],same.1.2.1,
      same.1.2.2.1,same.1.2.2.2.1,put_bytes_agree region same.1.2.2.2.2 _ _⟩,same.2⟩
  | exchangeIndex destination d =>
    have address : StringExecution.address mode (.exchangeIndex destination d) left d=
        StringExecution.address mode (.exchangeIndex destination d) right d := by
      simp only [StringExecution.address,StringExecution.nextPC,same.1.1]
    have loaded:=load_agree mode region same.1.2.2.2.2
      (StringExecution.address mode (.exchangeIndex destination d) right d) contained
    cases destination <;>
      simp only [StringExecution.execute,Bool.false_eq_true,ite_false,ite_true,AgreeState,
        RegionExecution.StateAgree,StringExecution.nextPC,address,same.1.1,same.1.2.1,
        same.1.2.2.1,same.1.2.2.2.1,same.2.1,same.2.2.1,same.2.2.2,loaded,true_and] <;>
      exact ⟨put_word_agree mode region same.1.2.2.2.2 _ _,True.intro⟩
  | subtractSmall d value =>
    have address : StringExecution.address mode (.subtractSmall d value) left d=
        StringExecution.address mode (.subtractSmall d value) right d := by
      simp only [StringExecution.address,StringExecution.nextPC,same.1.1]
    have loaded:=load_agree mode region same.1.2.2.2.2
      (StringExecution.address mode (.subtractSmall d value) right d) contained
    simp only [StringExecution.execute,Execution.storeState,AgreeState,RegionExecution.StateAgree,
      StringExecution.nextPC,address,same.1.1,same.1.2.1,same.1.2.2.1,same.2.1,same.2.2.1,same.2.2.2,loaded,true_and]
    exact ⟨put_word_agree mode region same.1.2.2.2.2 _ _,True.intro⟩
  | subtractFull d value =>
    have address : StringExecution.address mode (.subtractFull d value) left d=
        StringExecution.address mode (.subtractFull d value) right d := by
      simp only [StringExecution.address,StringExecution.nextPC,same.1.1]
    have loaded:=load_agree mode region same.1.2.2.2.2
      (StringExecution.address mode (.subtractFull d value) right d) contained
    simp only [StringExecution.execute,Execution.storeState,AgreeState,RegionExecution.StateAgree,
      StringExecution.nextPC,address,same.1.1,same.1.2.1,same.1.2.2.1,same.2.1,same.2.2.1,same.2.2.2,loaded,true_and]
    exact ⟨put_word_agree mode region same.1.2.2.2.2 _ _,True.intro⟩
  | move width =>
    have bytes:=bytes_agree region same.1.2.2.2.2 right.sourceIndex.toNat width contained
    simp only [StringExecution.execute,AgreeState,RegionExecution.StateAgree,StringExecution.nextPC,
      same.1.1,same.1.2.1,same.1.2.2.1,same.1.2.2.2.1,same.2.1,same.2.2.1,same.2.2.2,bytes,true_and]
    exact ⟨put_bytes_agree region same.1.2.2.2.2 _ _,True.intro⟩

theorem arithmetic_address_agrees (mode : Mode) (form : DwordArithmetic.Form)
    (left right : Execution.State mode) (pc : left.pc=right.pc) (ax : left.accumulator=right.accumulator) :
    DwordArithmetic.address mode form left=DwordArithmetic.address mode form right := by
  cases form <;> simp only [DwordArithmetic.address,DwordArithmetic.next,pc,ax]

theorem arithmetic_agrees (mode : Mode) (region : Region) (form : DwordArithmetic.Form)
    (left right : Execution.State mode) (same : RegionExecution.StateAgree mode region left right)
    (contained : Contained region (mixed mode (.arithmetic form) right)) :
    RegionExecution.StateAgree mode region (DwordArithmetic.execute mode form left) (DwordArithmetic.execute mode form right) := by
  have address:=arithmetic_address_agrees mode form left right same.1 same.2.1
  cases form
  all_goals simp only [Contained,mixed] at contained
  all_goals try have loaded:=dword_agree region same.2.2.2.2 _ contained
  all_goals simp only [RegionExecution.StateAgree,DwordArithmetic.execute,DwordArithmetic.next,
    DwordArithmetic.carry,DwordArithmetic.value,DwordArithmetic.prior,address,same.1,same.2.1,same.2.2.1,same.2.2.2.1]
  all_goals try simp only [loaded]
  all_goals simp only [DwordArithmetic.flag,DwordArithmetic.result,DwordCode.put,true_and]
  all_goals exact put_bytes_agree region same.2.2.2.2 _ _

theorem copy_agrees (mode : Mode) (region : Region) (form : DwordCode.Form mode)
    (left right : Execution.State mode) (same : RegionExecution.StateAgree mode region left right)
    (contained : Contained region (mixed mode (.copy form) right)) :
    RegionExecution.StateAgree mode region (DwordCode.execute mode form left) (DwordCode.execute mode form right) := by
  have address : DwordCode.address mode form left=DwordCode.address mode form right := by
    cases form <;> simp only [DwordCode.address,DwordCode.next,same.1]
  cases form
  all_goals simp only [Contained,mixed] at contained
  all_goals try have loaded:=dword_agree region same.2.2.2.2 _ contained
  all_goals simp only [RegionExecution.StateAgree,DwordCode.execute,DwordCode.next,address,
    same.1,same.2.1,same.2.2.1,same.2.2.2.1,DwordCode.put]
  all_goals try simp only [loaded]
  all_goals simp only [true_and]
  all_goals exact put_bytes_agree region same.2.2.2.2 _ _

theorem mixed_agrees (mode : Mode) (region : Region) (form : MixedDword.Form mode)
    (left right : StringExecution.State mode) (same : AgreeState mode region left right)
    (contained : Contained region (mixed mode form right.principal)) :
    AgreeState mode region {left with principal:=MixedDword.execute mode form left.principal}
      {right with principal:=MixedDword.execute mode form right.principal} := by
  cases form with
  | arithmetic form => exact ⟨arithmetic_agrees mode region form left.principal right.principal same.1 contained,same.2⟩
  | copy form => exact ⟨copy_agrees mode region form left.principal right.principal same.1 contained,same.2⟩
  | wideExchange d => exact ⟨RegionExecution.execute_agrees .x64 region (.memory .exchangeAcc d) left.principal right.principal same.1
      (native_within .x64 region _ right.principal contained),same.2⟩

theorem dword_effect_agrees (mode : Mode) (region : Region) (form : StringDword.Form mode)
    (left right : StringExecution.State mode) (same : AgreeState mode region left right)
    (contained : Contained region (dword mode form right)) :
    AgreeState mode region (StringDword.execute mode form left) (StringDword.execute mode form right) := by
  cases form with
  | string form => exact string_agrees mode region form left right same contained
  | mixed form => exact mixed_agrees mode region form left right same contained
  | xorAccumulator d =>
    have address : DwordXor.address mode d left.principal=DwordXor.address mode d right.principal := by
      simp only [DwordXor.address,DwordXor.next,same.1.1]
    have loaded:=dword_agree region same.1.2.2.2.2 _ contained
    simp only [StringDword.execute,AgreeState,RegionExecution.StateAgree,DwordXor.execute,DwordXor.next,
      address,same.1.1,same.1.2.1,same.1.2.2.1,same.2.1,same.2.2.1,same.2.2.2,loaded,DwordCode.put,true_and]
    exact ⟨put_bytes_agree region same.1.2.2.2.2 _ _,True.intro⟩

theorem control_agrees (mode : Mode) (region : Region) (form : StringControl.Form mode)
    (left right : StringExecution.State mode) (same : AgreeState mode region left right)
    (contained : Contained region (control mode form right)) :
    AgreeState mode region (StringControl.execute mode form left) (StringControl.execute mode form right) := by
  cases form with
  | previous form => exact dword_effect_agrees mode region form left right same contained
  | wideNegation d =>
    have address : WordNegation.address mode d left.principal=WordNegation.address mode d right.principal := by
      simp only [WordNegation.address,WordNegation.next,same.1.1]
    have loaded:=load_agree mode region same.1.2.2.2.2 _ contained
    simp only [StringControl.execute,AgreeState,RegionExecution.StateAgree,WordNegation.execute,WordNegation.next,
      address,same.1.1,same.1.2.1,same.1.2.2.1,same.2.1,same.2.2.1,same.2.2.2,loaded,true_and]
    exact ⟨put_word_agree mode region same.1.2.2.2.2 _ _,True.intro⟩

/-- Complete StringStack effects are independent of every exterior memory
completion once the actual single data-read window is contained. -/
theorem execute_agrees (mode : Mode) (region : Region) (form : StringStack.Form mode)
    (left right : StringExecution.State mode) (same : AgreeState mode region left right)
    (contained : Within mode region form right) :
    AgreeState mode region (StringStack.execute mode form left) (StringStack.execute mode form right) := by
  cases form with
  | previous form => exact control_agrees mode region form left right same contained
  | addSmall d value =>
    have address : WordAddImmediate.address mode d left.principal=WordAddImmediate.address mode d right.principal := by
      simp only [WordAddImmediate.address,WordAddImmediate.next,same.1.1]
    have loaded:=load_agree mode region same.1.2.2.2.2 _ contained
    simp only [StringStack.execute,AgreeState,RegionExecution.StateAgree,WordAddImmediate.execute,WordAddImmediate.next,
      Execution.storeState,address,same.1.1,same.1.2.1,same.1.2.2.1,same.2.1,same.2.2.1,same.2.2.2,loaded,true_and]
    exact ⟨put_word_agree mode region same.1.2.2.2.2 _ _,True.intro⟩

end SmcTuring.Native.StringReadAgreement
