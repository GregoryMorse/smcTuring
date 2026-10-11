module
public import SmcTuring.Appendix.Listing8GraphLayout

public section
namespace SmcTuring.Appendix.Listing8SourceGraph
open Native Listing8Prototypes

/-- Initial finite logical labels. None denotes the declared halt node;
continuation advances to the next packed rule, or halts at the table end. -/
structure Rule (transitions : Nat) where
  symbol : BitVec 32
  fresh : BitVec 32
  takeBack : Bool
  scanNext : Bool
  destination : Option (Fin transitions)
structure Node (nodes : Nat) where
  symbol : BitVec 32
  back : Fin nodes
  forward : Fin nodes
structure Graph where
  transitions : Nat
  nodes : Nat
  halt : Fin nodes
  rules : Fin transitions → Rule transitions
  tape : Fin nodes → Node nodes

@[expose] def nodePC (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes) :=
  Listing8GraphLayout.node mode origin g.transitions index.val
@[expose] def rulePC (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions) :=
  Listing8GraphLayout.transition mode origin index.val
@[expose] def statePC (mode : Mode) (origin : Nat) (g : Graph) : Option (Fin g.transitions) → Nat
  | none => nodePC mode origin g g.halt
  | some index => rulePC mode origin g index
@[expose] def nextPC (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions) :=
  if (g.rules index).scanNext=true ∧ index.val+1<g.transitions then
    Listing8GraphLayout.transition mode origin (index.val+1)
  else nodePC mode origin g g.halt
@[expose] def values (mode : Mode) (origin : Nat) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) : Listing8CopyImage.Values mode :=
  { tape := (g.tape node).symbol,rule := (g.rules rule).symbol,fresh := (g.rules rule).fresh,
    direction := if (g.rules rule).takeBack then BitVec.allOnes 32 else 0,
    back := Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).back),
    forward := Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).forward),
    next := Arithmetic.encodeNat mode (nextPC mode origin g rule),
    newState := Arithmetic.encodeNat mode (statePC mode origin g (g.rules rule).destination) }
@[expose] def table (mode : Mode) (origin : Nat) (g : Graph) :=
  List.ofFn (fun index : Fin g.transitions => values mode origin g g.halt index)

theorem table_length (mode : Mode) (origin : Nat) (g : Graph) :
    (table mode origin g).length=g.transitions := List.length_ofFn
theorem lookup (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions) :
    (table mode origin g)[index.val]?=some (values mode origin g g.halt index) := by
  simp only [table,List.getElem?_ofFn,index.isLt,dite_true]
theorem selected (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8TransitionTable.Selected mode (table mode origin g) rule.val (values mode origin g node rule) :=
  ⟨values mode origin g g.halt rule,lookup mode origin g rule,rfl,rfl,rfl,rfl,rfl⟩

end SmcTuring.Appendix.Listing8SourceGraph
