module
public import SmcTuring.Appendix.Listing8TMGraph
public import SmcTuring.Appendix.Listing8LoopIteration

public section
namespace SmcTuring.Appendix.Listing8TMScan
open Listing8SourceGraph Listing8TMRules Listing8TMGraph

/-- Concatenate actual logical interpreter iterations without changing their
intermediate graph, tape, head or rule. -/
theorem steps_append {g : Graph} {node : Fin g.nodes} {selected : Fin g.transitions} {count : Nat}
    {middle : Graph} {middleNode : Fin middle.nodes} {middleRule : Fin middle.transitions}
    {tailCount : Nat} {finalGraph : Graph} {finalNode : Fin finalGraph.nodes} {finalRule : Fin finalGraph.transitions}
    (first : Listing8LoopIteration.Steps g node selected count middle middleNode middleRule)
    (second : Listing8LoopIteration.Steps middle middleNode middleRule tailCount finalGraph finalNode finalRule) :
    Listing8LoopIteration.Steps g node selected (count+tailCount) finalGraph finalNode finalRule := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | next selected rest ih =>
    have joined:=Listing8LoopIteration.Steps.next selected (ih second)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

/-- Every skipped rule is an actual mismatch iteration. The induction proves
that all intervening tape and head values are retained. -/
theorem scan_to {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (first last : Fin (alphabet+1)) (count : Nat)
    (distance : first.val+count=last.val)
    (mismatches : ∀ slot : Fin (alphabet+1), first.val≤slot.val → slot.val<last.val →
      (rule machine (index state slot)).symbol≠encode (tape node)) :
    Listing8LoopIteration.Steps (graph machine halt back forward tape) node (index state first) count
      (graph machine halt back forward tape) node (index state last) := by
  induction count generalizing first with
  | zero =>
    have same : first=last := Fin.ext (by omega)
    subst first
    exact Listing8LoopIteration.Steps.refl _ _ _
  | succ count ih =>
    have before : first.val<alphabet := by have := last.isLt;omega
    have different:=mismatches first (Nat.le_refl _) (by omega)
    have rest:=ih (nextSlot first before) (by dsimp [nextSlot];omega)
      (fun slot lower upper => mismatches slot (by dsimp [nextSlot] at lower;omega) upper)
    refine Listing8LoopIteration.Steps.next (mismatch_next machine halt back forward tape node state first before different) ?_
    simp only [mismatch_node machine halt back forward tape node (index state first) different]
    dsimp only [Listing8GraphStep.updated]
    have sameTape :
        (fun query : Fin nodes => ({symbol:=Listing8GraphBodyNodes.symbol (graph machine halt back forward tape) node (index state first) query,back:=back query,forward:=forward query} : Node nodes))=
        (fun query => ({symbol:=encode (tape query),back:=back query,forward:=forward query} : Node nodes)) := by
      funext query
      rw [mismatch_symbol machine halt back forward tape node (index state first) different query]
    rw [sameTape]
    exact rest

theorem before_input {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (halt : Fin nodes) (back forward : Fin nodes → Fin nodes)
    (tape : Fin nodes → Fin alphabet) (node : Fin nodes) (state : Fin states) :
    Listing8LoopIteration.Steps (graph machine halt back forward tape) node (entry state) (tape node).val
      (graph machine halt back forward tape) node (index state (symbolSlot (tape node))) := by
  apply scan_to machine halt back forward tape node state ⟨0,by omega⟩ (symbolSlot (tape node)) (tape node).val (by simp only [symbolSlot,Nat.zero_add])
  intro slot lower upper
  have valid : slot.val<alphabet := by have := (tape node).isLt;change slot.val<(tape node).val at upper;omega
  have distinct : (⟨slot.val,valid⟩ : Fin alphabet)≠tape node := by
    intro same
    have observed:=congrArg Fin.val same
    change slot.val=(tape node).val at observed
    change slot.val<(tape node).val at upper
    omega
  exact different_symbol machine capacity state ⟨slot.val,valid⟩ (tape node) distinct

theorem missing_scan {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (halt : Fin nodes) (back forward : Fin nodes → Fin nodes)
    (tape : Fin nodes → Fin alphabet) (node : Fin nodes) (state : Fin states)
    (absent : machine.transition state (tape node)=none) :
    Listing8LoopIteration.Steps (graph machine halt back forward tape) node (entry state) alphabet
      (graph machine halt back forward tape) node (index state (endSlot alphabet)) := by
  apply scan_to machine halt back forward tape node state ⟨0,by omega⟩ (endSlot alphabet) alphabet (by simp only [endSlot,Nat.zero_add])
  intro slot lower upper
  have valid : slot.val<alphabet := upper
  by_cases same : (⟨slot.val,valid⟩ : Fin alphabet)=tape node
  · have missing : machine.transition state ⟨slot.val,valid⟩=none := by rw [same];exact absent
    exact missing_symbol machine capacity state ⟨slot.val,valid⟩ (tape node) missing
  · exact different_symbol machine capacity state ⟨slot.val,valid⟩ (tape node) same

/-- Empty state rule lists are included: all alphabet slots mismatch, the
explicit end rule halts, and the complete finite tape and head are unchanged. -/
theorem empty_state_halts {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (halt : Fin nodes) (back forward : Fin nodes → Fin nodes)
    (tape : Fin nodes → Fin alphabet) (node : Fin nodes) (state : Fin states)
    (empty : ∀ symbol, machine.transition state symbol=none) :
    Listing8LoopIteration.Steps (graph machine halt back forward tape) node (entry state) alphabet
      (graph machine halt back forward tape) node (index state (endSlot alphabet)) ∧
    Listing8GraphRun.Halted (graph machine halt back forward tape) node (index state (endSlot alphabet)) :=
  ⟨missing_scan machine capacity halt back forward tape node state (empty _),
   terminal_halted machine capacity halt back forward tape node state⟩

/-- A source transition is compiled to exactly input-symbol-value mismatch
iterations followed by one matched write/move/state iteration. -/
theorem transition {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (halt : Fin nodes) (back forward : Fin nodes → Fin nodes)
    (tape : Fin nodes → Fin alphabet) (node : Fin nodes) (state : Fin states)
    (fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state (tape node)=some (fresh,right,target)) :
    Listing8LoopIteration.Steps (graph machine halt back forward tape) node (entry state) ((tape node).val+1)
      (graph machine halt back forward (write tape node fresh))
      (if right then forward node else back node) (entry target) := by
  have skipped:=before_input machine capacity halt back forward tape node state
  have chosen : Listing8LoopIteration.Steps (graph machine halt back forward tape) node
      (index state (symbolSlot (tape node))) 1 (graph machine halt back forward (write tape node fresh))
      (if right then forward node else back node) (entry target) := by
    refine Listing8LoopIteration.Steps.next (selected_next machine halt back forward tape node state fresh right target selected) ?_
    simp only [selected_node machine halt back forward tape node state fresh right target selected]
    dsimp only [Listing8GraphStep.updated]
    have sameTape :
        (fun query : Fin nodes => ({symbol:=Listing8GraphBodyNodes.symbol (graph machine halt back forward tape) node (index state (symbolSlot (tape node))) query,back:=back query,forward:=forward query} : Node nodes))=
        (fun query => ({symbol:=encode (write tape node fresh query),back:=back query,forward:=forward query} : Node nodes)) := by
      funext query
      rw [selected_symbol machine halt back forward tape node state fresh right target selected query]
    rw [sameTape]
    exact Listing8LoopIteration.Steps.refl (graph machine halt back forward (write tape node fresh))
        (if right then forward node else back node) (entry target)
  exact steps_append skipped chosen

end SmcTuring.Appendix.Listing8TMScan
