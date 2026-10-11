module
public import SmcTuring.Appendix.Listing8GraphBodyNodes

public section
namespace SmcTuring.Appendix.Listing8GraphStep
open Native Listing8SourceGraph

@[expose] def scanRule (g : Graph) (rule : Fin g.transitions) : Option (Fin g.transitions) :=
  if valid : (g.rules rule).scanNext=true ∧ rule.val+1<g.transitions then
    some ⟨rule.val+1,valid.2⟩ else none
@[expose] def nextRule (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  if Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol then
    (g.rules rule).destination else scanRule g rule
@[expose] def nextNode (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  if Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol then
    (if (g.rules rule).takeBack then (g.tape node).back else (g.tape node).forward) else node
@[expose] def updated (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) : Graph :=
  {g with tape:=fun query => {g.tape query with symbol:=Listing8GraphBodyNodes.symbol g node rule query}}

theorem scan_pointer (mode : Mode) (origin : Nat) (g : Graph) (rule : Fin g.transitions) :
    statePC mode origin g (scanRule g rule)=nextPC mode origin g rule := by
  unfold scanRule nextPC
  split_ifs <;> rfl
theorem rule_pointer (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (if Listing8LiteralInput.chosen (values mode origin g node rule).rule (values mode origin g node rule).tape
      then (values mode origin g node rule).newState else (values mode origin g node rule).next)=
      Arithmetic.encodeNat mode (statePC mode origin g (nextRule g node rule)) := by
  cases chosen : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol <;>
    simp only [values,nextRule,chosen,Bool.false_eq_true,ite_false,ite_true]
  exact congrArg (Arithmetic.encodeNat mode) (scan_pointer mode origin g rule).symm
theorem head_pointer (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (if Listing8LiteralInput.chosen (values mode origin g node rule).rule (values mode origin g node rule).tape
      then (if (g.rules rule).takeBack then (values mode origin g node rule).back else (values mode origin g node rule).forward)
      else Arithmetic.encodeNat mode (nodePC mode origin g node))=
      Arithmetic.encodeNat mode (nodePC mode origin g (nextNode g node rule)) := by
  cases chosen : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol <;>
    cases direction : (g.rules rule).takeBack <;>
    simp only [values,nextNode,chosen,direction,Bool.false_eq_true,ite_false,ite_true]
theorem halted_iff (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    nextRule g node rule=none ↔ Listing8GraphRun.Halted g node rule := by
  by_cases same : (g.rules rule).symbol=(g.tape node).symbol
  · have chosen:= (Listing8GraphRun.chosen_iff g node rule).mpr same
    rw [nextRule,chosen]
    simp only [ite_true,Listing8GraphRun.Halted,same,true_and,ne_eq,not_true_eq_false,false_and,or_false]
  · have chosen : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol=false := by
      cases h : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol
      · rfl
      · exact False.elim (same ((Listing8GraphRun.chosen_iff g node rule).mp h))
    rw [nextRule,chosen]
    simp only [Bool.false_eq_true,ite_false,Listing8GraphRun.Halted,same,false_and,ne_eq,not_false_eq_true,true_and,false_or]
    unfold scanRule
    split_ifs with scan
    · simp only [false_iff]
      push Not
      exact ⟨scan.1,scan.2⟩
    · simp only [true_iff]
      push Not at scan
      by_cases allowed : (g.rules rule).scanNext=true
      · exact Or.inr (scan allowed)
      · exact Or.inl allowed
theorem node_value (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (query : Fin g.nodes) :
    Listing8GraphNodeImage.value mode origin (updated g node rule) query=
      Listing8GraphBodyNodes.value mode origin g node rule query := rfl
theorem node_declarations (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8GraphNodeImage.declarations mode origin (updated g node rule)=
      Listing8GraphBodyNodes.declarations mode origin g node rule := rfl
theorem node_label (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (query : Fin g.nodes) : nodePC mode origin (updated g node rule) query=nodePC mode origin g query := rfl
theorem rule_label (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (query : Fin g.transitions) : rulePC mode origin (updated g node rule) query=rulePC mode origin g query := rfl
theorem native_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8GraphPointers.Bounds mode origin (updated g node rule) := bounds
theorem transition_bytes (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (query : Fin g.transitions) (head : Fin g.nodes) :
    let v:=values mode origin (updated g node rule) head query
    Listing8Prototypes.transitionBytes mode (rulePC mode origin g query)
      v.next v.newState v.rule v.fresh v.direction=
      Listing8Prototypes.transitionBytes mode (rulePC mode origin g query)
        (values mode origin g g.halt query).next (values mode origin g g.halt query).newState
        (values mode origin g g.halt query).rule (values mode origin g g.halt query).fresh
        (values mode origin g g.halt query).direction := by
  cases target : (g.rules query).destination <;>
    simp only [values,updated,nextPC,statePC,nodePC,rulePC,target] <;> rfl

end SmcTuring.Appendix.Listing8GraphStep
