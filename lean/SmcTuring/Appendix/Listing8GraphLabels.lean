module
public import SmcTuring.Appendix.Listing8GraphStep

public section
namespace SmcTuring.Appendix.Listing8GraphLabels
open Native Listing8SourceGraph Listing8GraphStep

/-- Packed rule labels precede every node and remain distinct after native
encoding under the existing whole-image capacity bound. -/
theorem rule_not_halt (mode : Mode) (origin : Nat) (g : Graph) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Arithmetic.encodeNat mode (rulePC mode origin g rule)≠Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  intro same
  have address:=congrArg BitVec.toNat same
  rw [Listing8GraphPointers.rule_toNat mode origin g rule bounds,
    Listing8GraphPointers.node_toNat mode origin g g.halt bounds] at address
  have before:=Listing8GraphLayout.table_node_apart mode origin g.transitions rule.val g.halt.val rule.isLt
  change rulePC mode origin g rule+Listing8Prototypes.transitionSpan mode≤nodePC mode origin g g.halt at before
  have positive : 0<Listing8Prototypes.transitionSpan mode := by cases mode <;> decide
  omega
theorem state_halt_iff (mode : Mode) (origin : Nat) (g : Graph) (target : Option (Fin g.transitions))
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Arithmetic.encodeNat mode (statePC mode origin g target)=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) ↔ target=none := by
  cases target with
  | none => exact iff_of_true rfl rfl
  | some rule =>
    change Arithmetic.encodeNat mode (rulePC mode origin g rule)=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) ↔ _
    simp only [rule_not_halt mode origin g rule bounds,reduceCtorEq]
theorem native_halt_iff (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    (if Listing8LiteralInput.chosen (values mode origin g node rule).rule (values mode origin g node rule).tape
      then (values mode origin g node rule).newState else (values mode origin g node rule).next)=
      Arithmetic.encodeNat mode (nodePC mode origin g g.halt) ↔ Listing8GraphRun.Halted g node rule := by
  rw [rule_pointer,state_halt_iff mode origin g _ bounds,halted_iff]
theorem nonhalt_rule (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    ∃ target : Fin g.transitions,nextRule g node rule=some target := by
  cases result : nextRule g node rule with
  | none => exact False.elim (nonhalt ((halted_iff g node rule).mp result))
  | some target => exact ⟨target,rfl⟩

end SmcTuring.Appendix.Listing8GraphLabels
