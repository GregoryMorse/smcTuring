module
public import SmcTuring.Native.StringTemplateStates

public section
namespace SmcTuring.Native.JointTemplateStates

/-- Both certificates refer to exactly the same program and reached states. -/
theorem join (mode : Mode) (first second : StringExecution.State mode → Prop)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (a : StringTemplateStates.Run mode first forms state) (b : StringTemplateStates.Run mode second forms state) :
    StringTemplateStates.Run mode (fun reached => first reached ∧ second reached) forms state := by
  induction forms generalizing state with
  | nil => exact ⟨a,b⟩
  | cons form rest ih => exact ⟨⟨a.1,b.1⟩,ih _ a.2 b.2⟩

end SmcTuring.Native.JointTemplateStates
