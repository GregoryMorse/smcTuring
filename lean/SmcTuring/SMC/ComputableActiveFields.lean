module
public import SmcTuring.SMC.ConcreteActiveFields
public import Mathlib.Computability.Primrec.List

public section
namespace SmcTuring.SMC.Concrete

/-- The literal initializer's integer memory is the primitive-recursive identity. -/
theorem active_initial_memory_primrec : Primrec activeInitial.memory :=
  Primrec.id

/-- No unrestricted memory witness is chosen: the positive execution proof
starts from this fixed computable initializer. -/
theorem computably_initialized_unbounded_smc_witness :
    Primrec activeInitial.memory ∧ RunsForever activeInitial ∧
      PureComputation activeInitial ∧ InfinitelyChanges activeInitial ∧
      UnboundedChangedFields activeInitial :=
  ⟨active_initial_memory_primrec, pure_unbounded_smc_witness⟩

end SmcTuring.SMC.Concrete
