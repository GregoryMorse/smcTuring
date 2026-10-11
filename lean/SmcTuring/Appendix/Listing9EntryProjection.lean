module
public import SmcTuring.Appendix.Listing9ExecutionImage
public import SmcTuring.Appendix.Listing9CanonicalMapping

public section
namespace SmcTuring.Appendix.Listing9EntryProjection
open Native Listing8CopyImage Listing8SourceGraph Listing9PackedLayout

/-- Host initialization preserves exactly these modeled input registers and
CF. It installs the emitted memory and entry PC separately. -/
theorem initial_registers (mode : Mode) (start : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing9ExecutionImage.initial mode start l t g node rule backing seed).principal.accumulator=seed.principal.accumulator ∧
    (Listing9ExecutionImage.initial mode start l t g node rule backing seed).principal.stack=seed.principal.stack ∧
    (Listing9ExecutionImage.initial mode start l t g node rule backing seed).principal.carry=seed.principal.carry ∧
    (Listing9ExecutionImage.initial mode start l t g node rule backing seed).sourceIndex=seed.sourceIndex ∧
    (Listing9ExecutionImage.initial mode start l t g node rule backing seed).destinationIndex=seed.destinationIndex :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The host supplies forward string direction before the first instruction.
This initializer is not an executed CLD or a proof of preserving arbitrary DF. -/
theorem initial_direction (mode : Mode) (start : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing9ExecutionImage.initial mode start l t g node rule backing seed).backwards=false := rfl

theorem initial_pc (mode : Mode) (start : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Bounds mode start g.transitions g.nodes)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing9ExecutionImage.initial mode start l t g node rule backing seed).principal.pc.toNat=start := by
  change (Arithmetic.encodeNat mode start).toNat=start
  apply Arithmetic.encode_nat_toNat
  have cap:=bounds.capacity
  rw [Listing9PackedCapacity.endPC_exact] at cap
  omega

/-- A static mapped interval certifies the actual installed entry address.
The host still has to realize these effective permissions on physical hardware. -/
theorem initial_address (mode : Mode) (environment : MappedExecution.Environment) (start : Nat)
    (l : Layout) (t : Listing8PointerCopies.Targets) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Bounds mode start g.transitions g.nodes)
    (mapping : MappedExecution.Mapped mode environment ⟨start,endPC mode start g.transitions g.nodes⟩)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    AddressSpace.Valid mode environment.paging
      (Listing9ExecutionImage.initial mode start l t g node rule backing seed).principal.pc.toNat := by
  rw [initial_pc mode start l t g node rule bounds backing seed]
  apply AddressSpace.region_valid mode environment.paging ⟨start,endPC mode start g.transitions g.nodes⟩ mapping.fits start (Nat.le_refl _)
  change start<endPC mode start g.transitions g.nodes
  rw [Listing9PackedCapacity.endPC_exact]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

end SmcTuring.Appendix.Listing9EntryProjection
