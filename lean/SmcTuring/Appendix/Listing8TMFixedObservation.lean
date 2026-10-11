module
public import SmcTuring.Appendix.Listing8TMOutputWindow

public section
namespace SmcTuring.Appendix.Listing8TMFixedObservation
open Native Listing8SourceGraph Listing8TMRules Listing8TMWindow Listing8TMRun

/-- The output decoder is fixed by the emitted geometry and blank symbol.
Neither terminal rule values nor terminal tape values occur in its inputs. -/
@[expose] def observe {alphabet : Nat} (mode : Mode) (origin : Nat) (lower : Int)
    (blank : Fin alphabet) (transitions nodes : Nat) (memory : ByteMemory.Memory) (observed : Int) : BitVec 32 :=
  if inside : Inside lower nodes observed then
    DwordCode.get memory (Listing8GraphLayout.node mode origin transitions (headIndex lower nodes observed inside).val+6)
  else encode blank

theorem observe_graph {alphabet : Nat} (mode : Mode) (origin : Nat) (lower : Int)
    (blank : Fin alphabet) (g : Graph) (memory : ByteMemory.Memory) (observed : Int) :
    Listing8TMOutputWindow.observe mode origin lower blank g memory observed=
      observe mode origin lower blank g.transitions g.nodes memory observed := rfl

/-- Source configurations with the same fixed compilation geometry use
exactly the same decoder, even when their tape and state differ. -/
theorem configuration_independent {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (mode : Mode) (origin : Nat) (lower : Int) (nodes : Nat) (positive : 0<nodes)
    (first second : TM.Configuration alphabet states) (memory : ByteMemory.Memory) (observed : Int) :
    Listing8TMOutputWindow.observe mode origin lower machine.blank (graph machine lower nodes positive first) memory observed=
      Listing8TMOutputWindow.observe mode origin lower machine.blank (graph machine lower nodes positive second) memory observed := rfl

theorem reconstruct {alphabet states : Nat} (mode : Mode) (origin : Nat) (lower : Int)
    (blank : Fin alphabet) (g : Graph) (memory : ByteMemory.Memory) (source : TM.Configuration alphabet states)
    (cells : ∀ query : Fin g.nodes, DwordCode.get memory (nodePC mode origin g query+6)=encode (source.tape (position lower query)))
    (outside : ∀ observed, ¬Inside lower g.nodes observed → source.tape observed=blank) (observed : Int) :
    observe mode origin lower blank g.transitions g.nodes memory observed=encode (source.tape observed) :=
  Listing8TMOutputWindow.reconstruct mode origin lower blank g memory source cells outside observed

end SmcTuring.Appendix.Listing8TMFixedObservation
