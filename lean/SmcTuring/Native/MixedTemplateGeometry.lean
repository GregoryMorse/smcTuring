module
public import SmcTuring.Native.MixedFixedTemplates

public section
namespace SmcTuring.Native.MixedTemplateGeometry

@[expose] def windows (mode : Mode) : Nat → List (MixedDword.Form mode) → List (Nat × Nat)
  | _,[] => []
  | pc,form::rest => (pc,MixedDword.length mode form)::windows mode (pc+MixedDword.length mode form) rest

theorem conjunction (mode : Mode) (first second : StringExecution.State mode → Prop)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (a : StringTemplateStates.Run mode first forms state) (b : StringTemplateStates.Run mode second forms state) :
    StringTemplateStates.Run mode (fun reached => first reached ∧ second reached) forms state := by
  induction forms generalizing state with
  | nil => exact ⟨a,b⟩
  | cons form rest ih => exact ⟨⟨a.1,b.1⟩,ih _ a.2 b.2⟩

theorem copy_windows (mode : Mode) (layout : DwordLayout.Layout) :
    windows mode layout.start ((DwordLayout.program mode layout).map MixedDword.Form.copy)=
      (MixedFixedTemplates.copyEntries mode layout).map (fun entry => (entry.pc,MixedFixedTemplates.span mode entry)) := by
  cases mode <;> rfl

end SmcTuring.Native.MixedTemplateGeometry
