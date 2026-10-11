module
public import SmcTuring.Appendix.Listing8TMScan

public section
namespace SmcTuring.Appendix.Listing8TMWindow
open Listing8SourceGraph Listing8TMRules

@[expose] def position (lower : Int) {width : Nat} (node : Fin width) : Int := lower+node.val
@[expose] def back {width : Nat} (node : Fin width) : Fin width :=
  ⟨node.val-1,by have := node.isLt;omega⟩
@[expose] def forward {width : Nat} (node : Fin width) : Fin width :=
  if inside : node.val+1<width then ⟨node.val+1,inside⟩ else node
@[expose] def tape {alphabet states width : Nat} (lower : Int) (source : TM.Configuration alphabet states) :
    Fin width → Fin alphabet := fun node => source.tape (position lower node)
abbrev graph {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (lower : Int) (width : Nat) (positive : 0<width) (source : TM.Configuration alphabet states) : Graph :=
  Listing8TMGraph.graph machine ⟨0,positive⟩ back forward (tape lower source)

@[expose] def Inside (lower : Int) (width : Nat) (head : Int) : Prop := lower≤head ∧ head<lower+width
@[expose] def headIndex (lower : Int) (width : Nat) (head : Int) (inside : Inside lower width head) : Fin width :=
  ⟨(head-lower).toNat,by dsimp [Inside] at inside;omega⟩

theorem position_injective (lower : Int) {width : Nat} (first second : Fin width) :
    position lower first=position lower second ↔ first=second := by
  constructor
  · intro same;apply Fin.ext;dsimp [position] at same;omega
  · intro same;rw [same]
theorem position_headIndex (lower : Int) (width : Nat) (head : Int) (inside : Inside lower width head) :
    position lower (headIndex lower width head inside)=head := by
  have lowerBound : lower≤head := inside.1
  dsimp [position,headIndex]
  omega
theorem position_back (lower : Int) {width : Nat} (node : Fin width) (away : 0<node.val) :
    position lower (back node)=position lower node-1 := by
  dsimp [position,back];omega
theorem position_forward (lower : Int) {width : Nat} (node : Fin width) (away : node.val+1<width) :
    position lower (forward node)=position lower node+1 := by
  simp only [forward,away,dite_true,position]
  omega

/-- Every cell of the finite window reflects the actual source tape update,
including all cells other than the current head. -/
theorem tape_write {alphabet states width : Nat} (lower : Int) (source : TM.Configuration alphabet states)
    (node : Fin width) (head : position lower node=source.head) (fresh : Fin alphabet) :
    write (tape lower source) node fresh=
      (fun query : Fin width => write source.tape source.head fresh (position lower query)) := by
  funext query
  by_cases same : query=node
  · subst query;simp only [read_write_same,head]
  · have different : position lower query≠source.head := by
      rw [←head];exact fun equality => same ((position_injective lower query node).mp equality)
    simp only [read_write_other _ _ _ _ same,read_write_other _ _ _ _ different,tape]

/-- Compile an actual TM transition to the interpreter's logical Steps.
Only the present head and finite window margins are required; the reached
head, entire tape and next-state entry are derived. -/
theorem step {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (lower : Int) (width : Nat) (positive : 0<width) (source finish : TM.Configuration alphabet states)
    (node : Fin width) (head : position lower node=source.head)
    (leftMargin : lower<source.head) (rightMargin : source.head+1<lower+width)
    (actual : TM.step machine source=some finish) :
    ∃ nextNode : Fin width, position lower nextNode=finish.head ∧
      Listing8LoopIteration.Steps (graph machine lower width positive source) node (entry source.state)
        ((source.tape source.head).val+1) (graph machine lower width positive finish) nextNode (entry finish.state) := by
  cases selected : machine.transition source.state (source.tape source.head) with
  | none => simp [TM.step,selected] at actual
  | some result =>
    rcases result with ⟨fresh,right,target⟩
    have resultEq : finish={state:=target,head:=if right then source.head+1 else source.head-1,tape:=write source.tape source.head fresh} := by
      have known:=TM.transition_correct machine source fresh right target selected
      rw [known] at actual
      exact (Option.some.inj actual).symm
    subst finish
    have tapeHead : tape (width:=width) lower source node=source.tape source.head := by rw [tape,head]
    have chosen : machine.transition source.state (tape (width:=width) lower source node)=some (fresh,right,target) := by rw [tapeHead];exact selected
    have logical:=Listing8TMScan.transition machine capacity (⟨0,positive⟩ : Fin width) back forward
      (tape lower source) node source.state fresh right target chosen
    refine ⟨if right then forward node else back node,?_,?_⟩
    · cases right
      · exact (position_back lower node (by dsimp [position] at head;omega)).trans (by rw [head];rfl)
      · exact (position_forward lower node (by dsimp [position] at head;omega)).trans (by rw [head];rfl)
    · rw [tape_write lower source node head fresh] at logical
      rw [tapeHead] at logical
      exact logical

end SmcTuring.Appendix.Listing8TMWindow
