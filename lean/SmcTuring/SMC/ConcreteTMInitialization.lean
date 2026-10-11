module
public import SmcTuring.SMC.ConcreteInitialization
public import SmcTuring.Dolan.Scan

public section

namespace SmcTuring.SMC.Concrete

open Dolan

/-- The unbounded SMC image is fixed. Its initial words are computed from a
finite transition table and finite input through the checked Dolan initializer. -/
@[expose] def initialTMState {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) : State :=
  initialState (Mov.initialKernelState machine (TM.initialConfiguration machine input))

theorem initial_tm_static {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) : Static (initialTMState machine input) := initial_static _

theorem initial_tm_rep {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) :
    Virtual.Rep dataLayout (Mov.initialKernelState machine (TM.initialConfiguration machine input))
      (initialTMState machine input) ∧
    Mov.ScanRep machine (TM.initialConfiguration machine input) 0
      (Mov.initialKernelState machine (TM.initialConfiguration machine input)) :=
  ⟨initial_rep _, Mov.initial_scan_correct _ _⟩

end SmcTuring.SMC.Concrete
