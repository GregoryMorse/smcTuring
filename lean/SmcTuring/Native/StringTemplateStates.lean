module
public import SmcTuring.Native.StringWrites

public section
namespace SmcTuring.Native.StringTemplateStates

/-- A property at every reached boundary, including the initial and final
states. This includes intermediate architectural stores inside a helper. -/
@[expose] def Run (mode : Mode) (property : StringExecution.State mode → Prop) :
    List (StringStack.Form mode) → StringExecution.State mode → Prop
  | [],state => property state
  | form::rest,state => property state ∧ Run mode property rest (StringStack.execute mode form state)

theorem append (mode : Mode) (property : StringExecution.State mode → Prop)
    (first second : List (StringStack.Form mode)) (state : StringExecution.State mode) :
    Run mode property (first++second) state ↔
      Run mode property first state ∧ Run mode property second (StringWrites.run mode first state) := by
  induction first generalizing state with
  | nil =>
    change Run mode property second state ↔ property state ∧ Run mode property second state
    cases second with
    | nil => exact ⟨fun h => ⟨h,h⟩,fun h => h.2⟩
    | cons => exact ⟨fun h => ⟨h.1,h⟩,fun h => h.2⟩
  | cons form rest ih =>
    change (property state ∧ Run mode property (rest++second) (StringStack.execute mode form state)) ↔ _
    rw [ih]
    simp only [Run,StringWrites.run,and_assoc]

theorem at_prefix (mode : Mode) (property : StringExecution.State mode → Prop)
    (first second : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (allStates : Run mode property (first++second) state) :
    property (StringWrites.run mode first state) := by
  have later := ((append mode property first second state).mp allStates).2
  cases second with
  | nil => exact later
  | cons => exact later.1

theorem monotone (mode : Mode) (firstProperty secondProperty : StringExecution.State mode → Prop)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (implies : ∀ state,firstProperty state → secondProperty state)
    (allStates : Run mode firstProperty forms state) : Run mode secondProperty forms state := by
  induction forms generalizing state with
  | nil => exact implies state allStates
  | cons form rest ih => exact ⟨implies state allStates.1,ih _ allStates.2⟩

end SmcTuring.Native.StringTemplateStates
