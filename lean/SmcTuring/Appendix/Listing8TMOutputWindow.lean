module
public import SmcTuring.Appendix.Listing8TMObservedRun

public section
namespace SmcTuring.Appendix.Listing8TMOutputWindow
open Native Listing8SourceGraph Listing8TMRules Listing8TMWindow Listing8TMRun

instance (lower : Int) (width : Nat) (head : Int) : Decidable (Inside lower width head) :=
  inferInstanceAs (Decidable (lower≤head ∧ head<lower+width))

/-- Observe the finite emitted tape, with the declared blank symbol outside
its window. This is an explicit mathematical output contract. -/
@[expose] def observe {alphabet : Nat} (mode : Mode) (origin : Nat) (lower : Int)
    (blank : Fin alphabet) (g : Graph) (memory : ByteMemory.Memory) (observed : Int) : BitVec 32 :=
  if inside : Inside lower g.nodes observed then
    DwordCode.get memory (nodePC mode origin g (headIndex lower g.nodes observed inside)+6)
  else encode blank

/-- The source run cannot modify a position outside its initial fixed
window. Every head move and write in the induction follows TM.step. -/
theorem run_frame {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (source finish : TM.Configuration alphabet states) (count : Nat) (lower : Int) (width : Nat)
    (leftMargin : lower+(count : Int)<source.head) (rightMargin : source.head+(count : Int)+1<lower+width)
    (actual : TM.run machine count source=some finish) (observed : Int)
    (outside : ¬Inside lower width observed) : finish.tape observed=source.tape observed := by
  induction count generalizing source with
  | zero =>
    have same : source=finish := Option.some.inj actual
    rw [same]
  | succ count ih =>
    cases first : TM.step machine source with
    | none => simp [TM.run,first] at actual
    | some middle =>
      have tail : TM.run machine count middle=some finish := by simpa only [TM.run,first,Option.bind_some] using actual
      cases selected : machine.transition source.state (source.tape source.head) with
      | none => simp [TM.step,selected] at first
      | some result =>
        rcases result with ⟨fresh,right,target⟩
        have known:=TM.transition_correct machine source fresh right target selected
        rw [known] at first
        have equality:=Option.some.inj first
        subst middle
        have different : observed≠source.head := by dsimp [Inside] at outside;omega
        have retained:=ih {state:=target,head:=if right then source.head+1 else source.head-1,tape:=write source.tape source.head fresh}
          (by cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega)
          (by cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega) tail
        rw [retained]
        exact read_write_other source.tape source.head observed fresh different

theorem initial_outside_blank {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) (extent : Nat) (covered : input.length≤extent) (observed : Int)
    (outside : ¬Inside (lower (TM.initialConfiguration machine input) extent) (width extent) observed) :
    (TM.initialConfiguration machine input).tape observed=machine.blank := by
  by_cases negative : observed<0
  · simp [TM.initialConfiguration,negative]
  · have far : input.length≤observed.toNat := by
      dsimp [Inside,lower,width,TM.initialConfiguration] at outside
      omega
    have absent : input[observed.toNat]?=none := by simp [far]
    simp only [TM.initialConfiguration,negative,ite_false,absent,Option.getD_none]

/-- The enlarged window includes the full input and every visited position.
All terminal source cells outside it are blank, proved from actual execution. -/
theorem terminal_outside_blank {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (observed : Int)
    (outside : ¬Inside (lower (TM.initialConfiguration machine input) (count+input.length)) (width (count+input.length)) observed) :
    finish.tape observed=machine.blank := by
  rw [run_frame machine (TM.initialConfiguration machine input) finish count
    (lower (TM.initialConfiguration machine input) (count+input.length)) (width (count+input.length))
    (by dsimp [lower];omega) (by dsimp [lower,width];omega) actual observed outside]
  exact initial_outside_blank machine input (count+input.length) (by omega) observed outside

theorem reconstruct {alphabet states : Nat} (mode : Mode) (origin : Nat) (lower : Int)
    (blank : Fin alphabet) (g : Graph) (memory : ByteMemory.Memory) (source : TM.Configuration alphabet states)
    (cells : ∀ query : Fin g.nodes, DwordCode.get memory (nodePC mode origin g query+6)=encode (source.tape (position lower query)))
    (outside : ∀ observed, ¬Inside lower g.nodes observed → source.tape observed=blank) (observed : Int) :
    observe mode origin lower blank g memory observed=encode (source.tape observed) := by
  unfold observe
  split_ifs with inside
  · rw [cells,position_headIndex]
  · rw [outside observed inside]

end SmcTuring.Appendix.Listing8TMOutputWindow
