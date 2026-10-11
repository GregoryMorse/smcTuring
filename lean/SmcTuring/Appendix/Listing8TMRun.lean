module
public import SmcTuring.Appendix.Listing8TMWindow

public section
namespace SmcTuring.Appendix.Listing8TMRun
open Listing8SourceGraph Listing8TMRules Listing8TMWindow

/-- A completed finite source run fits a fixed finite tape window. The margin
is only an initial geometric inequality; every reached configuration, native
rule scan, tape update and head label is derived by induction. -/
theorem run {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (lower : Int) (width : Nat) (positive : 0<width) (source finish : TM.Configuration alphabet states)
    (node : Fin width) (head : position lower node=source.head) (count : Nat)
    (leftMargin : lower+(count : Int)<source.head) (rightMargin : source.head+(count : Int)+1<lower+width)
    (actual : TM.run machine count source=some finish) :
    ∃ (iterations : Nat) (lastNode : Fin width), iterations≤count*alphabet ∧ position lower lastNode=finish.head ∧
      Listing8LoopIteration.Steps (graph machine lower width positive source) node (entry source.state) iterations
        (graph machine lower width positive finish) lastNode (entry finish.state) := by
  induction count generalizing source node with
  | zero =>
    have same : source=finish := Option.some.inj actual
    subst finish
    exact ⟨0,node,by omega,head,Listing8LoopIteration.Steps.refl _ _ _⟩
  | succ count ih =>
    cases first : TM.step machine source with
    | none => simp [TM.run,first] at actual
    | some middle =>
      have tail : TM.run machine count middle=some finish := by simpa only [TM.run,first,Option.bind_some] using actual
      have move : middle.head=source.head+1 ∨ middle.head=source.head-1 := by
        cases selected : machine.transition source.state (source.tape source.head) with
        | none => simp [TM.step,selected] at first
        | some result =>
          rcases result with ⟨fresh,right,target⟩
          have known:=TM.transition_correct machine source fresh right target selected
          rw [known] at first
          have eq:=Option.some.inj first
          have observed:=congrArg TM.Configuration.head eq
          cases right
          · right;exact observed.symm
          · left;exact observed.symm
      obtain ⟨nextNode,nextHead,initialSteps⟩:=Listing8TMWindow.step machine capacity lower width positive source middle node head (by omega) (by omega) first
      obtain ⟨iterations,lastNode,bounded,lastHead,rest⟩:=ih middle nextNode nextHead
        (by rcases move with right | left <;> omega) (by rcases move with right | left <;> omega) tail
      refine ⟨(source.tape source.head).val+1+iterations,lastNode,?_,lastHead,
        Listing8TMScan.steps_append initialSteps rest⟩
      have symbolBound:= (source.tape source.head).isLt
      rw [Nat.add_mul,Nat.one_mul]
      omega

@[expose] def lower {alphabet states : Nat} (source : TM.Configuration alphabet states) (count : Nat) : Int :=
  source.head-count-1
@[expose] def width (count : Nat) : Nat := 2*count+3
theorem positive (count : Nat) : 0<width count := by dsimp [width];omega
@[expose] def firstNode (count : Nat) : Fin (width count) := ⟨count+1,by dsimp [width];omega⟩
abbrev initialGraph {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (source : TM.Configuration alphabet states) (count : Nat) :=
  graph machine (lower source count) (width count) (positive count) source

theorem first_head {alphabet states : Nat} (source : TM.Configuration alphabet states) (count : Nat) :
    position (lower source count) (firstNode count)=source.head := by
  dsimp [position,lower,firstNode];omega

/-- The finite window and its starting head are constructed from the prefix
length. No visited-head trace or later tape observation is a premise. -/
theorem finite_prefix {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (source finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count source=some finish) :
    ∃ (iterations : Nat) (lastNode : Fin (width count)), iterations≤count*alphabet ∧
      position (lower source count) lastNode=finish.head ∧
      Listing8LoopIteration.Steps (initialGraph machine source count) (firstNode count) (entry source.state) iterations
        (graph machine (lower source count) (width count) (positive count) finish) lastNode (entry finish.state) :=
  run machine capacity (lower source count) (width count) (positive count) source finish (firstNode count)
    (first_head source count) count (by dsimp [lower];omega) (by dsimp [lower,width];omega) actual

/-- Source halting, including an empty initial state rule list, supplies the
actual final declared halt required by the complete native interpreter. The
terminal mismatch iteration preserves every tape cell and the logical head. -/
theorem finite_halt {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (source finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count source=some finish) (halted : TM.step machine finish=none) :
    ∃ (iterations : Nat) (lastNode : Fin (width count)), iterations≤count*alphabet+alphabet ∧
      position (lower source count) lastNode=finish.head ∧
      Listing8LoopIteration.Steps (initialGraph machine source count) (firstNode count) (entry source.state) iterations
        (graph machine (lower source count) (width count) (positive count) finish) lastNode (index finish.state (endSlot alphabet)) ∧
      Listing8GraphRun.Halted (graph machine (lower source count) (width count) (positive count) finish)
        lastNode (index finish.state (endSlot alphabet)) ∧
      Listing8GraphStep.updated (graph machine (lower source count) (width count) (positive count) finish)
        lastNode (index finish.state (endSlot alphabet))=
        graph machine (lower source count) (width count) (positive count) finish := by
  obtain ⟨iterations,lastNode,bounded,head,logical⟩:=finite_prefix machine capacity source finish count actual
  have absent : machine.transition finish.state (finish.tape finish.head)=none := by
    cases chosen : machine.transition finish.state (finish.tape finish.head) with
    | none => rfl
    | some result => simp only [TM.step,chosen,Option.some_ne_none] at halted
  have tapeHead : tape (width:=width count) (lower source count) finish lastNode=finish.tape finish.head := by rw [tape,head]
  have missing : machine.transition finish.state (tape (width:=width count) (lower source count) finish lastNode)=none := by rw [tapeHead];exact absent
  have tail:=Listing8TMScan.missing_scan machine capacity (⟨0,positive count⟩ : Fin (width count)) back forward
    (tape (lower source count) finish) lastNode finish.state missing
  refine ⟨iterations+alphabet,lastNode,by omega,head,Listing8TMScan.steps_append logical tail,
    Listing8TMGraph.terminal_halted machine capacity _ back forward _ lastNode finish.state,?_⟩
  exact Listing8TMGraph.mismatch_updated machine _ back forward _ lastNode _
    (terminal_symbol machine capacity finish.state _)

end SmcTuring.Appendix.Listing8TMRun
