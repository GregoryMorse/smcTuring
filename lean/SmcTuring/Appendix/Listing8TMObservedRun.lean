module
public import SmcTuring.Appendix.Listing8TMRun

public section
namespace SmcTuring.Appendix.Listing8TMObservedRun
open Listing8SourceGraph Listing8TMRules Listing8TMWindow Listing8TMRun

/-- The window may include additional input or output positions. Padding is
finite initial data; source execution still performs exactly count steps. -/
theorem finite_prefix {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (source finish : TM.Configuration alphabet states) (count padding : Nat)
    (actual : TM.run machine count source=some finish) :
    ∃ (iterations : Nat) (lastNode : Fin (width (count+padding))), iterations≤count*alphabet ∧
      position (lower source (count+padding)) lastNode=finish.head ∧
      Listing8LoopIteration.Steps (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) iterations
        (graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish) lastNode (entry finish.state) :=
  Listing8TMRun.run machine capacity (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) source finish
    (firstNode (count+padding)) (first_head source (count+padding)) count (by dsimp [lower];omega) (by dsimp [lower,width];omega) actual

/-- Source halting supplies the final declared native halt in the larger
window; additional input cells and every other window cell are retained. -/
theorem finite_halt {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (source finish : TM.Configuration alphabet states) (count padding : Nat)
    (actual : TM.run machine count source=some finish) (halted : TM.step machine finish=none) :
    ∃ (iterations : Nat) (lastNode : Fin (width (count+padding))), iterations≤count*alphabet+alphabet ∧
      position (lower source (count+padding)) lastNode=finish.head ∧
      Listing8LoopIteration.Steps (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) iterations
        (graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish) lastNode (index finish.state (endSlot alphabet)) ∧
      Listing8GraphRun.Halted (graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish)
        lastNode (index finish.state (endSlot alphabet)) ∧
      Listing8GraphStep.updated (graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish)
        lastNode (index finish.state (endSlot alphabet))=
        graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish := by
  obtain ⟨iterations,lastNode,bounded,head,logical⟩:=finite_prefix machine capacity source finish count padding actual
  have absent : machine.transition finish.state (finish.tape finish.head)=none := by
    cases chosen : machine.transition finish.state (finish.tape finish.head) with
    | none => rfl
    | some result => simp only [TM.step,chosen,Option.some_ne_none] at halted
  have tapeHead : tape (width:=width (count+padding)) (lower source (count+padding)) finish lastNode=finish.tape finish.head := by rw [tape,head]
  have missing : machine.transition finish.state (tape (width:=width (count+padding)) (lower source (count+padding)) finish lastNode)=none := by rw [tapeHead];exact absent
  have tail:=Listing8TMScan.missing_scan machine capacity (⟨0,positive (count+padding)⟩ : Fin (width (count+padding))) back forward
    (tape (lower source (count+padding)) finish) lastNode finish.state missing
  refine ⟨iterations+alphabet,lastNode,by omega,head,Listing8TMScan.steps_append logical tail,
    Listing8TMGraph.terminal_halted machine capacity _ back forward _ lastNode finish.state,?_⟩
  exact Listing8TMGraph.mismatch_updated machine _ back forward _ lastNode _
    (terminal_symbol machine capacity finish.state _)


end SmcTuring.Appendix.Listing8TMObservedRun
