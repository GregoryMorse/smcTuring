module
public import SmcTuring.Appendix.Listing8PackedFieldBounds

public section
namespace SmcTuring.Appendix.Listing8PackedContext
open Native Listing8SourceGraph Listing8Prototypes Listing8CopyImage Listing8PackedBodyLayout Listing8PackedResources

theorem input_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8GlobalInput.Bounds mode (layout mode origin g node rule) (targets mode origin) := by
  have before:=before_table mode origin
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  refine ⟨Listing8PackedFieldBounds.input_fields mode origin g node rule native,joined mode origin g node rule,?_,?_⟩
  · intro pc member
    rw [input_end]
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals cases mode <;> simp
  · intro copy member
    rw [Listing8PackedPointerBounds.dword_layouts] at member
    cases mode
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply Or.inl
    all_goals change _≤nodePC _ origin g node
    all_goals simp only [reduceCtorEq,ite_true,ite_false] at before
    all_goals dsimp
    all_goals omega

theorem direction_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8DirectionGeometry.Bounds mode (layout mode origin g node rule) (targets mode origin) := by
  have coords:=direction_labels mode origin g node rule
  have body:=body_capacity mode origin g node native
  have before:=before_table mode origin
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin rule.val
  change Listing8FullTableImage.start mode origin≤rulePC mode origin g rule at ruleAfter
  refine ⟨input_bounds mode origin g node rule native,?_,coords.1,coords.2.1,coords.2.2.1,coords.2.2.2.1,?_,?_,?_,?_⟩
  · rw [coords.2.2.2.2]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body ⊢ <;> omega
  · rw [coords.2.2.2.2]
    cases mode <;> simp [layout,input]
  · rw [coords.2.2.2.2]
    cases mode <;> simp [targets]
  · apply Or.inr
    rw [coords.2.2.2.2]
    change main mode origin+(if mode=.x86 then 597 else 932)≤nodePC mode origin g node
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega
  · apply Or.inr
    rw [coords.2.2.2.2]
    change main mode origin+(if mode=.x86 then 597 else 932)≤rulePC mode origin g rule
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega

theorem state_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8StateGeometry.Bounds mode (layout mode origin g node rule) (targets mode origin) := by
  have coords:=state_labels mode origin g node rule
  have body:=body_capacity mode origin g node native
  have before:=before_table mode origin
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin rule.val
  change Listing8FullTableImage.start mode origin≤rulePC mode origin g rule at ruleAfter
  refine ⟨direction_bounds mode origin g node rule native,?_,coords.1,coords.2.1,?_,?_⟩
  · rw [coords.2.2]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body ⊢ <;> omega
  · apply Or.inr
    rw [coords.2.2]
    change main mode origin+(if mode=.x86 then 644 else 1028)≤nodePC mode origin g node
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega
  · apply Or.inr
    rw [coords.2.2]
    change main mode origin+(if mode=.x86 then 644 else 1028)≤rulePC mode origin g rule
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega

theorem failure_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8FailureGeometry.Bounds mode (layout mode origin g node rule) (targets mode origin)
      (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) := by
  have body:=body_capacity mode origin g node native
  have before:=before_table mode origin
  have haltAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g g.halt
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin rule.val
  change Listing8FullTableImage.start mode origin≤rulePC mode origin g rule at ruleAfter
  refine ⟨state_bounds mode origin g node rule native,?_,Listing8GraphPointers.node_capacity mode origin g g.halt native,?_,?_,?_⟩
  · rw [failure_end];exact body
  · apply Or.inr
    rw [failure_region]
    cases mode <;> simp [Listing8FailureLayout.comparisonPC,Listing8FailureLayout.ownerPC,StringCodec.initialSize] <;>
      simp only [reduceCtorEq,ite_true,ite_false] at before <;> omega
  · apply Or.inr
    rw [failure_end]
    change main mode origin+(if mode=.x86 then 754 else 1177)≤nodePC mode origin g node
    exact Nat.le_trans before nodeAfter
  · apply Or.inr
    rw [failure_end]
    change main mode origin+(if mode=.x86 then 754 else 1177)≤rulePC mode origin g rule
    exact Nat.le_trans before ruleAfter

theorem boot_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8BootImage.Bounds mode origin (layout mode origin g node rule) := by
  have before:=before_table mode origin
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin rule.val
  change Listing8FullTableImage.start mode origin≤rulePC mode origin g rule at ruleAfter
  refine ⟨rfl,Or.inr ?_,Or.inr ?_⟩
  · change main mode origin≤nodePC mode origin g node;omega
  · change main mode origin≤rulePC mode origin g rule;omega

/-- Construct every static Context field from the packed graph capacity and
reset reach. No helper layout, copied target or body resource is an input. -/
theorem context (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8GraphInputContext.Context mode origin (layout mode origin g node rule) (targets mode origin) g node rule :=
  ⟨rfl,rfl,resources mode origin g node rule native,Listing8PackedFieldBounds.graph_fields mode origin g node rule native,
   Listing8PackedPointerBounds.bounds mode origin g node rule native,boot_bounds mode origin g node rule,
   failure_bounds mode origin g node rule native,native⟩

end SmcTuring.Appendix.Listing8PackedContext
