module
public import SmcTuring.Appendix.Listing8SourceGraph

public section
namespace SmcTuring.Appendix.Listing8GraphPointers
open Native Listing8Prototypes Listing8SourceGraph
abbrev Bounds (mode : Mode) (origin : Nat) (g : Graph) :=
  Listing8GraphLayout.Bounds mode origin g.transitions g.nodes

theorem node_capacity (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes)
    (bounds : Bounds mode origin g) : nodePC mode origin g index+mode.wordBytes<2^(8*mode.wordBytes) := by
  have cap:=Listing8GraphLayout.node_capacity mode origin g.transitions g.nodes index.val bounds index.isLt
  have size : mode.wordBytes≤nodeSpan mode := by cases mode <;> decide
  change nodePC mode origin g index+nodeSpan mode<_ at cap
  omega
theorem rule_capacity (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Bounds mode origin g) : rulePC mode origin g index+mode.wordBytes<2^(8*mode.wordBytes) := by
  have cap:=Listing8GraphLayout.transition_capacity mode origin g.transitions g.nodes index.val bounds index.isLt
  have size : mode.wordBytes≤transitionSpan mode := by cases mode <;> decide
  change rulePC mode origin g index+transitionSpan mode<_ at cap
  omega
theorem node_toNat (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes)
    (bounds : Bounds mode origin g) : (Arithmetic.encodeNat mode (nodePC mode origin g index)).toNat=nodePC mode origin g index := by
  apply Arithmetic.encode_nat_toNat
  have cap:=node_capacity mode origin g index bounds
  omega
theorem rule_toNat (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Bounds mode origin g) : (Arithmetic.encodeNat mode (rulePC mode origin g index)).toNat=rulePC mode origin g index := by
  apply Arithmetic.encode_nat_toNat
  have cap:=rule_capacity mode origin g index bounds
  omega
theorem state_capacity (mode : Mode) (origin : Nat) (g : Graph) (target : Option (Fin g.transitions))
    (bounds : Bounds mode origin g) : statePC mode origin g target+mode.wordBytes<2^(8*mode.wordBytes) := by
  cases target with
  | none => exact node_capacity mode origin g g.halt bounds
  | some index => exact rule_capacity mode origin g index bounds
theorem state_toNat (mode : Mode) (origin : Nat) (g : Graph) (target : Option (Fin g.transitions))
    (bounds : Bounds mode origin g) : (Arithmetic.encodeNat mode (statePC mode origin g target)).toNat=statePC mode origin g target := by
  apply Arithmetic.encode_nat_toNat
  have cap:=state_capacity mode origin g target bounds
  omega
theorem next_capacity (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Bounds mode origin g) : nextPC mode origin g index+mode.wordBytes<2^(8*mode.wordBytes) := by
  unfold nextPC
  split_ifs with scan
  · exact rule_capacity mode origin g ⟨index.val+1,scan.2⟩ bounds
  · exact node_capacity mode origin g g.halt bounds
theorem next_toNat (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Bounds mode origin g) : (Arithmetic.encodeNat mode (nextPC mode origin g index)).toNat=nextPC mode origin g index := by
  apply Arithmetic.encode_nat_toNat
  have cap:=next_capacity mode origin g index bounds
  omega

theorem node_monotone (mode : Mode) (origin : Nat) (g : Graph) (first second : Fin g.nodes)
    (before : first.val≤second.val) : nodePC mode origin g first≤nodePC mode origin g second := by
  have mult:=Nat.mul_le_mul_right (nodeSpan mode) before
  dsimp [nodePC,Listing8GraphLayout.node]
  omega
theorem rule_monotone (mode : Mode) (origin : Nat) (g : Graph) (first second : Fin g.transitions)
    (before : first.val≤second.val) : rulePC mode origin g first≤rulePC mode origin g second := by
  have mult:=Nat.mul_le_mul_right (transitionSpan mode) before
  dsimp [rulePC,Listing8GraphLayout.transition]
  omega

/-- This includes self-neighbors: the symbol window precedes either reader. -/
theorem node_outside (mode : Mode) (origin : Nat) (g : Graph) (owner target : Fin g.nodes) (offset : Nat)
    (afterSymbol : mode.wordBytes≤offset) (inside : offset+pointerSpan mode≤nodeSpan mode) :
    nodePC mode origin g target+mode.wordBytes≤nodePC mode origin g owner+offset ∨
      nodePC mode origin g owner+offset+pointerSpan mode≤nodePC mode origin g target := by
  by_cases before : target.val≤owner.val
  · have prior:=node_monotone mode origin g target owner before
    left;omega
  · have later:=Listing8GraphLayout.nodes_apart mode origin g.transitions owner.val target.val (by omega)
    change nodePC mode origin g owner+nodeSpan mode≤nodePC mode origin g target at later
    right;omega

theorem next_after (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions) :
    rulePC mode origin g index+transitionSpan mode≤nextPC mode origin g index := by
  unfold nextPC
  split_ifs with scan
  · exact Listing8GraphLayout.transitions_apart mode origin index.val (index.val+1) (by omega)
  · exact Listing8GraphLayout.table_node_apart mode origin g.transitions index.val g.halt.val index.isLt

theorem state_outside (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (target : Option (Fin g.transitions)) :
    statePC mode origin g target+mode.wordBytes≤stateEntry mode (rulePC mode origin g index) ∨
      stateEntry mode (rulePC mode origin g index)+pointerSpan mode≤statePC mode origin g target := by
  have endEq : stateEntry mode (rulePC mode origin g index)+pointerSpan mode=
      rulePC mode origin g index+transitionSpan mode := by
    dsimp [stateEntry,directionEntry,newEntry,currentEntry,transitionSpan];omega
  cases target with
  | none =>
    right
    rw [endEq]
    exact Listing8GraphLayout.table_node_apart mode origin g.transitions index.val g.halt.val index.isLt
  | some target =>
    change rulePC mode origin g target+mode.wordBytes≤_ ∨ _≤rulePC mode origin g target
    by_cases before : target.val≤index.val
    · have prior:=rule_monotone mode origin g target index before
      have size : mode.wordBytes≤pointerSpan mode+30 := by cases mode <;> decide
      left
      dsimp [stateEntry,directionEntry,newEntry,currentEntry]
      omega
    · right
      rw [endEq]
      exact Listing8GraphLayout.transitions_apart mode origin index.val target.val (by omega)

theorem transition_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Bounds mode origin g) :
    Listing8TransitionBlock.Bounds mode (rulePC mode origin g rule) (values mode origin g node rule) := by
  refine ⟨Listing8GraphLayout.transition_capacity mode origin g.transitions g.nodes rule.val bounds rule.isLt,?_,?_⟩
  · simp only [values]
    rw [next_toNat mode origin g rule bounds]
    right
    have afterEntry:=next_after mode origin g rule
    dsimp [transitionSpan] at afterEntry
    omega
  · simp only [values]
    rw [state_toNat mode origin g (g.rules rule).destination bounds]
    exact state_outside mode origin g rule (g.rules rule).destination

end SmcTuring.Appendix.Listing8GraphPointers
