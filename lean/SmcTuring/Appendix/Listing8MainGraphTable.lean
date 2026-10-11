module
public import SmcTuring.Appendix.Listing8GraphStep

public section
namespace SmcTuring.Appendix.Listing8MainGraphTable
open Native Listing8CopyImage Listing8SourceGraph

/-- Only the five rule fields are encoded in a transition declaration.
Tape symbols and neighbor values carried by Values do not enter these bytes. -/
structure SameFields (mode : Mode) (first second : Values mode) : Prop where
  next : first.next=second.next
  newState : first.newState=second.newState
  rule : first.rule=second.rule
  fresh : first.fresh=second.fresh
  direction : first.direction=second.direction

theorem bytes_ofFn_congr (mode : Mode) (count : Nat) (first second : Fin count → Values mode)
    (same : ∀ index,SameFields mode (first index) (second index)) (start : Nat) :
    Listing8TransitionTable.bytes mode start (List.ofFn first)=Listing8TransitionTable.bytes mode start (List.ofFn second) := by
  induction count generalizing start with
  | zero => simp only [List.ofFn_zero,Listing8TransitionTable.bytes]
  | succ count ih =>
    rw [List.ofFn_succ,List.ofFn_succ,Listing8TransitionTable.bytes,Listing8TransitionTable.bytes,
      (same 0).next,(same 0).newState,(same 0).rule,(same 0).fresh,(same 0).direction]
    rw [ih (fun index => first index.succ) (fun index => second index.succ) (fun index => same index.succ)]

theorem updated_table_bytes (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (start : Nat) :
    Listing8TransitionTable.bytes mode start (table mode origin (Listing8GraphStep.updated g node rule))=
      Listing8TransitionTable.bytes mode start (table mode origin g) := by
  apply bytes_ofFn_congr
  intro index
  refine ⟨rfl,?_,rfl,rfl,rfl⟩
  cases target : (g.rules index).destination <;>
    simp only [values,Listing8GraphStep.updated,nextPC,statePC,nodePC,rulePC,target] <;> rfl

theorem updated_table_current (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (memory : ByteMemory.Memory) (current : Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) memory) :
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin (Listing8GraphStep.updated g node rule)) memory := by
  rw [Listing8TransitionTable.Initial,updated_table_bytes]
  exact current

end SmcTuring.Appendix.Listing8MainGraphTable
