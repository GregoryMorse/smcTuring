module
public import SmcTuring.Appendix.Listing9FullExecution

public section
namespace SmcTuring.Appendix.Listing9Fallthrough
open Native Listing9PackedLayout Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem save_positive (mode : Mode) (start transitions nodes : Nat) : 0<(layout mode start transitions nodes).save := by
  have ordered:=bounds_order mode start transitions nodes
  have positive : 0<origin mode start := by cases mode <;> dsimp [origin,AccumulatorLayout.storeSize] <;> omega
  omega

theorem save_fits (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) :
    (layout mode start transitions nodes).save<2^(8*mode.wordBytes) := by
  have ordered:=bounds_order mode start transitions nodes
  have cap:=bounds.capacity
  omega

theorem encoded_save_nonzero (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) :
    Arithmetic.encodeNat mode (layout mode start transitions nodes).save≠0 := by
  intro zero
  have numeric:=congrArg BitVec.toNat zero
  rw [Arithmetic.encode_nat_toNat mode _ (save_fits mode start transitions nodes bounds)] at numeric
  change (layout mode start transitions nodes).save=0 at numeric
  have positive:=save_positive mode start transitions nodes
  omega

/-- Full fallthrough preserves seed RAX exactly in the self-address case.
The epilogue boundary restores arbitrary full seed RAX earlier in the trace. -/
theorem x64_preserved_iff (start transitions nodes : Nat) (bounds : Bounds .x64 start transitions nodes)
    (state : StringExecution.State .x64) (entry : state.principal.pc=Arithmetic.encodeNat .x64 (saveOwner .x64 start transitions nodes))
    (current : Listing9Storage.Current .x64 start transitions nodes state.principal.memory) :
    (Listing9Storage.finish .x64 start transitions nodes state).principal.accumulator=state.principal.accumulator ↔
      state.principal.accumulator=Arithmetic.encodeNat .x64 (layout .x64 start transitions nodes).save := by
  rw [Listing9Storage.effect .x64 start transitions nodes bounds state entry current]
  simp only [reduceCtorEq,ite_false,eq_comm]


/-- Every admitted finite logical halt/static placement with zero seed RAX
has an actual full native trace restoring zero at the epilogue boundary and
then reaching the complete emitted end with nonzero RAX. No future packet,
value or trace observation is assumed. This is a bounded native claim. -/
theorem zero_seed_trace (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context .x64 (origin .x64 start) l t g node rule)
    (bounds : Bounds .x64 start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State .x64)
    (zero : seed.principal.accumulator=0) :
    ∃ (restored finalState : StringExecution.State .x64) (prefixCode : List (StringStack.Form .x64)),
      StringStack.Trace .x64 (Listing9FullExecution.initial .x64 start l t g node rule memory seed) prefixCode restored ∧
      restored.principal.accumulator=0 ∧
      StringStack.Trace .x64 (Listing9FullExecution.initial .x64 start l t g node rule memory seed)
        (prefixCode++Listing9Storage.program .x64 start g.transitions g.nodes) finalState ∧
      finalState.principal.pc.toNat=endPC .x64 start g.transitions g.nodes ∧
      finalState.principal.accumulator=Arithmetic.encodeNat .x64 (layout .x64 start g.transitions g.nodes).save ∧
      finalState.principal.accumulator≠0 := by
  obtain ⟨restored,finalState,prefixCode,first,ax,_,actual,endpoint,_,value,_⟩:=
    Listing9FullExecution.execute .x64 start l t logical halted ctx bounds memory seed
  have finalValue : finalState.principal.accumulator=Arithmetic.encodeNat .x64 (layout .x64 start g.transitions g.nodes).save := by
    simpa only [reduceCtorEq,ite_false] using value
  exact ⟨restored,finalState,prefixCode,first,ax.trans zero,actual,endpoint,finalValue,
    finalValue ▸ encoded_save_nonzero .x64 start g.transitions g.nodes bounds⟩

end SmcTuring.Appendix.Listing9Fallthrough
