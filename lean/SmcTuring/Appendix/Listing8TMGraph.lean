module
public import SmcTuring.Appendix.Listing8TMRules

public section
namespace SmcTuring.Appendix.Listing8TMGraph
open Listing8SourceGraph Listing8TMRules

/-- Compile a finite tape window, its neighbor labels and the complete machine
rule table to the actual graph consumed by the printed interpreter. -/
abbrev graph {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet) : Graph :=
  {transitions:=states*(alphabet+1),nodes:=nodes,halt:=halt,rules:=rule machine,
   tape:=fun node => {symbol:=encode (tape node),back:=back node,forward:=forward node}}

@[expose] def nextSlot {alphabet : Nat} (slot : Fin (alphabet+1)) (before : slot.val<alphabet) : Fin (alphabet+1) :=
  ⟨slot.val+1,by omega⟩

theorem scan {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (state : Fin states) (slot : Fin (alphabet+1)) (before : slot.val<alphabet) :
    Listing8GraphStep.scanRule (graph machine halt back forward tape) (index state slot)=
      some (index state (nextSlot slot before)) := by
  have allowed:=scan_allowed machine state slot before
  have location : (index state (nextSlot slot before)).val=(index state slot).val+1 := by
    simp only [index_value,nextSlot];omega
  have inside : (index state slot).val+1<states*(alphabet+1) := by
    rw [←location];exact (index state (nextSlot slot before)).isLt
  change (if valid : (rule machine (index state slot)).scanNext=true ∧ (index state slot).val+1<states*(alphabet+1)
    then some (⟨(index state slot).val+1,valid.2⟩ : Fin (states*(alphabet+1))) else none)=some (index state (nextSlot slot before))
  rw [dite_eq_left ⟨allowed,inside⟩]
  exact congrArg some (Fin.ext location.symm)

theorem stop_scan {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (state : Fin states) :
    Listing8GraphStep.scanRule (graph machine halt back forward tape) (index state (endSlot alphabet))=none := by
  change (if valid : (rule machine (index state (endSlot alphabet))).scanNext=true ∧ (index state (endSlot alphabet)).val+1<states*(alphabet+1)
    then some (⟨(index state (endSlot alphabet)).val+1,valid.2⟩ : Fin (states*(alphabet+1))) else none)=none
  have stop : ¬((rule machine (index state (endSlot alphabet))).scanNext=true ∧ (index state (endSlot alphabet)).val+1<states*(alphabet+1)) := by
    rw [terminal];simp
  rw [dite_eq_right stop]

theorem mismatch_chosen {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (selected : Fin (states*(alphabet+1)))
    (different : (rule machine selected).symbol≠encode (tape node)) :
    Listing8LiteralInput.chosen ((graph machine halt back forward tape).rules selected).symbol
      ((graph machine halt back forward tape).tape node).symbol=false := by
  cases h : Listing8LiteralInput.chosen ((graph machine halt back forward tape).rules selected).symbol
      ((graph machine halt back forward tape).tape node).symbol with
  | false => rfl
  | true => exact False.elim (different ((Listing8GraphRun.chosen_iff (graph machine halt back forward tape) node selected).mp h))

theorem mismatch_node {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (selected : Fin (states*(alphabet+1)))
    (different : (rule machine selected).symbol≠encode (tape node)) :
    Listing8GraphStep.nextNode (graph machine halt back forward tape) node selected=node := by
  rw [Listing8GraphStep.nextNode,mismatch_chosen machine halt back forward tape node selected different]
  rfl

theorem mismatch_updated {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (selected : Fin (states*(alphabet+1)))
    (different : (rule machine selected).symbol≠encode (tape node)) :
    Listing8GraphStep.updated (graph machine halt back forward tape) node selected=graph machine halt back forward tape := by
  have chosen:=mismatch_chosen machine halt back forward tape node selected different
  simp only [Listing8GraphStep.updated,Listing8GraphBodyNodes.symbol,chosen,Bool.false_eq_true,ite_false]
  congr 1
  funext query
  by_cases same : query=node
  · subst query;simp only [ite_self]
  · simp only [same,ite_false]

theorem mismatch_symbols {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (selected : Fin (states*(alphabet+1)))
    (different : (rule machine selected).symbol≠encode (tape node)) :
    Listing8GraphBodyNodes.symbol (graph machine halt back forward tape) node selected=
      (fun query => encode (tape query)) := by
  have chosen:=mismatch_chosen machine halt back forward tape node selected different
  funext query
  simp only [Listing8GraphBodyNodes.symbol,chosen,Bool.false_eq_true,ite_false]
  by_cases same : query=node
  · subst query;simp only [ite_self]
  · simp only [same,ite_false]

theorem mismatch_symbol {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (selected : Fin (states*(alphabet+1)))
    (different : (rule machine selected).symbol≠encode (tape node)) (query : Fin nodes) :
    Listing8GraphBodyNodes.symbol (graph machine halt back forward tape) node selected query=encode (tape query) :=
  congrFun (mismatch_symbols machine halt back forward tape node selected different) query

theorem mismatch_next {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (slot : Fin (alphabet+1)) (before : slot.val<alphabet)
    (different : (rule machine (index state slot)).symbol≠encode (tape node)) :
    Listing8GraphStep.nextRule (graph machine halt back forward tape) node (index state slot)=
      some (index state (nextSlot slot before)) := by
  rw [Listing8GraphStep.nextRule,mismatch_chosen machine halt back forward tape node (index state slot) different]
  exact scan machine halt back forward tape state slot before

theorem selected_chosen {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state (tape node)=some (fresh,right,target)) :
    Listing8LiteralInput.chosen ((graph machine halt back forward tape).rules (index state (symbolSlot (tape node)))).symbol
      ((graph machine halt back forward tape).tape node).symbol=true := by
  apply (Listing8GraphRun.chosen_iff (graph machine halt back forward tape) node (index state (symbolSlot (tape node)))).mpr
  change (rule machine _).symbol=encode (tape node)
  rw [active machine state (tape node) fresh right target selected]

theorem selected_next {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state (tape node)=some (fresh,right,target)) :
    Listing8GraphStep.nextRule (graph machine halt back forward tape) node (index state (symbolSlot (tape node)))=
      some (entry target) := by
  rw [Listing8GraphStep.nextRule,selected_chosen machine halt back forward tape node state fresh right target selected]
  simp only [ite_true,graph,active machine state (tape node) fresh right target selected]

theorem selected_node {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state (tape node)=some (fresh,right,target)) :
    Listing8GraphStep.nextNode (graph machine halt back forward tape) node (index state (symbolSlot (tape node)))=
      if right then forward node else back node := by
  rw [Listing8GraphStep.nextNode,selected_chosen machine halt back forward tape node state fresh right target selected]
  simp only [ite_true,graph,active machine state (tape node) fresh right target selected]
  cases right <;> rfl

theorem selected_updated {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state (tape node)=some (fresh,right,target)) :
    Listing8GraphStep.updated (graph machine halt back forward tape) node (index state (symbolSlot (tape node)))=
      graph machine halt back forward (write tape node fresh) := by
  have chosen:=selected_chosen machine halt back forward tape node state fresh right target selected
  simp only [Listing8GraphStep.updated,Listing8GraphBodyNodes.symbol,chosen,ite_true]
  change {transitions:=_,nodes:=_,halt:=_,rules:=_,tape:=_}=graph machine halt back forward (write tape node fresh)
  simp only [graph,active machine state (tape node) fresh right target selected]
  congr 1
  funext query
  by_cases same : query=node
  · subst query;simp only [ite_true,read_write_same]
  · simp only [same,ite_false,read_write_other tape node query fresh same]

theorem selected_symbols {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state (tape node)=some (fresh,right,target)) :
    Listing8GraphBodyNodes.symbol (graph machine halt back forward tape) node (index state (symbolSlot (tape node)))=
      (fun query => encode (write tape node fresh query)) := by
  have chosen:=selected_chosen machine halt back forward tape node state fresh right target selected
  funext query
  simp only [Listing8GraphBodyNodes.symbol,chosen,ite_true]
  simp only [active machine state (tape node) fresh right target selected]
  by_cases same : query=node
  · subst query;simp only [ite_true,read_write_same]
  · simp only [same,ite_false,read_write_other tape node query fresh same]

theorem selected_symbol {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (halt : Fin nodes) (back forward : Fin nodes → Fin nodes) (tape : Fin nodes → Fin alphabet)
    (node : Fin nodes) (state : Fin states) (fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state (tape node)=some (fresh,right,target)) (query : Fin nodes) :
    Listing8GraphBodyNodes.symbol (graph machine halt back forward tape) node (index state (symbolSlot (tape node))) query=
      encode (write tape node fresh query) :=
  congrFun (selected_symbols machine halt back forward tape node state fresh right target selected) query

theorem terminal_halted {alphabet states nodes : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (halt : Fin nodes) (back forward : Fin nodes → Fin nodes)
    (tape : Fin nodes → Fin alphabet) (node : Fin nodes) (state : Fin states) :
    Listing8GraphRun.Halted (graph machine halt back forward tape) node (index state (endSlot alphabet)) := by
  apply (Listing8GraphStep.halted_iff (graph machine halt back forward tape) node (index state (endSlot alphabet))).mp
  rw [Listing8GraphStep.nextRule,mismatch_chosen machine halt back forward tape node _ (terminal_symbol machine capacity state (tape node))]
  exact stop_scan machine halt back forward tape state

end SmcTuring.Appendix.Listing8TMGraph
