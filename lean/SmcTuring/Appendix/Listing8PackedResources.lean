module
public import SmcTuring.Appendix.Listing8PackedBodyLayout

public section
namespace SmcTuring.Appendix.Listing8PackedResources
open Native Listing8SourceGraph Listing8Prototypes Listing8CopyImage Listing8PackedBodyLayout

/-- All fixed body fragments fit once the declared graph fits. -/
theorem body_capacity (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    main mode origin+(if mode=.x86 then 754 else 1177)<2^(8*mode.wordBytes) := by
  have before:=before_table mode origin
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have fits:=Listing8GraphLayout.node_capacity mode origin g.transitions g.nodes node.val bounds node.isLt
  change nodePC mode origin g node+nodeSpan mode<_ at fits
  have positive : 0<nodeSpan mode := by cases mode <;> decide
  omega

theorem fixed_range (mode : Mode) (origin next target : Nat)
    (nextLower : main mode origin≤next) (nextUpper : next≤main mode origin+(if mode=.x86 then 754 else 1177))
    (targetLower : main mode origin≤target) (targetUpper : target≤main mode origin+(if mode=.x86 then 754 else 1177)) :
    Relocation.SignedDelta next target := by
  have small : (if mode=.x86 then 754 else 1177)≤1177 := by cases mode <;> decide
  unfold Relocation.SignedDelta Relocation.delta
  constructor <;> omega

theorem node_resources (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    TemplateCopy.Resources mode (nodeParams mode (layout mode origin g node rule)) := by
  have body:=body_capacity mode origin g node bounds
  have before:=before_table mode origin
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have copied:=copy_positions mode origin g node rule
  have ends:=Listing8Initializer.code_geometry mode (layout mode origin g node rule)
  have fits:=Listing8GraphLayout.node_capacity mode origin g.transitions g.nodes node.val bounds node.isLt
  change nodePC mode origin g node+nodeSpan mode<_ at fits
  have size : mode.wordBytes≤nodeSpan mode := by cases mode <;> decide
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change nodeSpan mode<2^31;cases mode <;> decide
  · change secondStart mode (layout mode origin g node rule)<_
    rw [ends.1]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body ⊢ <;> omega
  · change nodePC mode origin g node+max (nodeSpan mode) mode.wordBytes<_
    rw [Nat.max_eq_left size];exact fits
  · change (nodeParams mode (layout mode origin g node rule)).destination+max (nodeSpan mode) mode.wordBytes<_
    rw [Nat.max_eq_left size,copied.1]
    cases mode <;> simp [nodeSpan,pointerSpan,ReaderImage.totalSize] at body ⊢ <;> omega
  · apply Or.inr
    change (nodeParams mode (layout mode origin g node rule)).destination+nodeSpan mode≤nodePC mode origin g node
    rw [copied.1]
    cases mode <;> simp [nodeSpan,pointerSpan,ReaderImage.totalSize] at before ⊢ <;> omega
  · apply Or.inr
    change secondStart mode (layout mode origin g node rule)≤nodePC mode origin g node
    rw [ends.1]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega
  · apply Or.inr
    change secondStart mode (layout mode origin g node rule)≤(nodeParams mode (layout mode origin g node rule)).destination
    rw [ends.1,copied.1]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

theorem transition_resources (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    TemplateCopy.Resources mode (transitionParams mode (layout mode origin g node rule)) := by
  have body:=body_capacity mode origin g node bounds
  have before:=before_table mode origin
  have after:=Listing8GraphLayout.transition_lower mode origin rule.val
  change Listing8FullTableImage.start mode origin≤rulePC mode origin g rule at after
  have copied:=copy_positions mode origin g node rule
  have ends:=Listing8Initializer.code_geometry mode (layout mode origin g node rule)
  have fits:=Listing8GraphLayout.transition_capacity mode origin g.transitions g.nodes rule.val bounds rule.isLt
  change rulePC mode origin g rule+transitionSpan mode<_ at fits
  have size : mode.wordBytes≤transitionSpan mode := by cases mode <;> decide
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change transitionSpan mode<2^31;cases mode <;> decide
  · change patchStart mode (layout mode origin g node rule)<_
    rw [ends.2.1]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body ⊢ <;> omega
  · change rulePC mode origin g rule+max (transitionSpan mode) mode.wordBytes<_
    rw [Nat.max_eq_left size];exact fits
  · change (transitionParams mode (layout mode origin g node rule)).destination+max (transitionSpan mode) mode.wordBytes<_
    rw [Nat.max_eq_left size,copied.2.1]
    cases mode <;> simp [transitionSpan,pointerSpan,ReaderImage.totalSize] at body ⊢ <;> omega
  · apply Or.inr
    change (transitionParams mode (layout mode origin g node rule)).destination+transitionSpan mode≤rulePC mode origin g rule
    rw [copied.2.1]
    cases mode <;> simp [transitionSpan,pointerSpan,ReaderImage.totalSize] at before ⊢ <;> omega
  · apply Or.inr
    change patchStart mode (layout mode origin g node rule)≤rulePC mode origin g rule
    rw [ends.2.1]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega
  · apply Or.inr
    change patchStart mode (layout mode origin g node rule)≤(transitionParams mode (layout mode origin g node rule)).destination
    rw [ends.2.1,copied.2.1]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

theorem resources (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) : Resources mode (layout mode origin g node rule) := by
  have body:=body_capacity mode origin g node bounds
  have before:=before_table mode origin
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin rule.val
  change Listing8FullTableImage.start mode origin≤rulePC mode origin g rule at ruleAfter
  have copied:=copy_positions mode origin g node rule
  refine ⟨node_resources mode origin g node rule bounds,transition_resources mode origin g node rule bounds,?_,?_,?_,?_,?_⟩
  · rw [copied.2.2]
    change main mode origin+(if mode=.x86 then 299 else 421)≤main mode origin+(if mode=.x86 then 367 else 550)
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  · rw [input_end]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body ⊢ <;> omega
  · apply Or.inr
    rw [input_end]
    change main mode origin+(if mode=.x86 then 506 else 730)≤nodePC mode origin g node
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega
  · apply Or.inr
    rw [input_end]
    change main mode origin+(if mode=.x86 then 506 else 730)≤rulePC mode origin g rule
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before ⊢ <;> omega
  · exact Or.inr (Listing8GraphLayout.table_node_apart mode origin g.transitions rule.val node.val rule.isLt)

end SmcTuring.Appendix.Listing8PackedResources
