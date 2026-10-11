module
public import SmcTuring.Native.MixedSequenceTemplateRuns

public section
namespace SmcTuring.Native.StringStoreRegions

@[expose] def Run (mode : Mode) (allowed : Nat → Nat → Prop) :
    List (StringStack.Form mode) → StringExecution.State mode → Prop
  | [],_ => True
  | form::rest,state =>
      allowed (StringWrites.packet mode form state).address (StringWrites.packet mode form state).bytes.length ∧
        Run mode allowed rest (StringStack.execute mode form state)

theorem append (mode : Mode) (allowed : Nat → Nat → Prop)
    (first second : List (StringStack.Form mode)) (state : StringExecution.State mode) :
    Run mode allowed (first++second) state ↔
      Run mode allowed first state ∧ Run mode allowed second (StringWrites.run mode first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,Run,StringWrites.run,true_and]
  | cons form rest ih => simp only [List.cons_append,Run,StringWrites.run,ih,and_assoc]

theorem bounded_packet (mode : Mode) (allowed : Nat → Nat → Prop) (field : Nat)
    (form : StringStack.Form mode) (state : StringExecution.State mode)
    (writes : StringWrites.CodeWrite mode field (field+4) form state)
    (length : (StringWrites.packet mode form state).bytes.length=4) (owned : allowed field 4) :
    allowed (StringWrites.packet mode form state).address (StringWrites.packet mode form state).bytes.length := by
  have address : (StringWrites.packet mode form state).address=field := by
    have lower := writes.2.1;have upper := writes.2.2
    rw [length] at upper
    omega
  rw [address,length]
  exact owned

theorem mixed (mode : Mode) (allowed : Nat → Nat → Prop) (forms : List (MixedDword.Form mode))
    (state : StringExecution.State mode) (owned : MixedDword.OwnedRun mode allowed forms state.principal) :
    Run mode allowed ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    constructor
    · simpa only [StringMixedWrites.address,StringMixedWrites.length] using owned.1
    · change Run mode allowed _ (StringDword.execute mode (StringMixed.canonical mode form) state)
      rw [StringMixed.execute]
      exact ih _ owned.2

theorem arithmetic_states (mode : Mode) (templates : List DwordTemplateCollection.Template)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (initial : DwordTemplateCollection.All templates state.principal.memory)
    (owned : Run mode (DwordTemplateCollection.CompatibleAll templates) forms state) :
    StringTemplateStates.Run mode (fun reached => DwordTemplateCollection.All templates reached.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact initial
  | cons form rest ih =>
    have kept : DwordTemplateCollection.All templates (StringStack.execute mode form state).principal.memory := by
      rw [StringWrites.execute_memory]
      exact DwordTemplateCollection.store_all templates state.principal.memory _ _ initial owned.1
    exact ⟨initial,ih _ kept owned.2⟩

theorem fixed_states (mode : Mode) (templates : List (MixedFixedTemplates.Entry mode))
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (initial : MixedFixedTemplates.All mode templates state.principal.memory)
    (owned : Run mode (MixedFixedTemplates.OutsideAll mode templates) forms state) :
    StringTemplateStates.Run mode (fun reached => MixedFixedTemplates.All mode templates reached.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact initial
  | cons form rest ih =>
    have kept : MixedFixedTemplates.All mode templates (StringStack.execute mode form state).principal.memory := by
      rw [StringWrites.execute_memory]
      exact MixedFixedTemplates.store_all mode templates state.principal.memory _ _ initial owned.1
    exact ⟨initial,ih _ kept owned.2⟩

end SmcTuring.Native.StringStoreRegions
