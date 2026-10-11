module
public import SmcTuring.Appendix.Listing9PackedCapacity
public import SmcTuring.Native.MappedExecution

public section
namespace SmcTuring.Appendix.Listing9CanonicalMapping
open Native AddressSpace MemoryRegion MappedExecution

/-- Finite word capacity plus one canonical component for x64 certifies the
whole literal emitted Listing 9 interval. Word capacity alone is insufficient. -/
theorem fits (mode : Mode) (paging : Paging) (start transitions nodes : Nat)
    (bounds : Listing9PackedLayout.Bounds mode start transitions nodes)
    (canonical : mode=.x64 → Listing9PackedLayout.endPC mode start transitions nodes≤half paging ∨ highStart paging≤start) :
    Fits mode paging ⟨start,Listing9PackedLayout.endPC mode start transitions nodes⟩ := by
  have capacity:=bounds.capacity
  cases mode with
  | x86 => change Listing9PackedLayout.endPC .x86 start transitions nodes≤2^32; exact Nat.le_of_lt capacity
  | x64 =>
    change Listing9PackedLayout.endPC .x64 start transitions nodes≤half paging ∨
      (highStart paging≤start ∧ Listing9PackedLayout.endPC .x64 start transitions nodes≤2^64)
    rcases canonical rfl with low | high
    · exact Or.inl low
    · exact Or.inr ⟨high,Nat.le_of_lt capacity⟩

/-- Read/write/execute bits here are effective permissions supplied by the
host. Their implementation by real paging and segmentation is external. -/
theorem mapped (mode : Mode) (environment : Environment) (start transitions nodes : Nat)
    (bounds : Listing9PackedLayout.Bounds mode start transitions nodes)
    (canonical : mode=.x64 → Listing9PackedLayout.endPC mode start transitions nodes≤half environment.paging ∨ highStart environment.paging≤start)
    (readable : ∀ address, start≤address → address<Listing9PackedLayout.endPC mode start transitions nodes → environment.readable address=true)
    (writable : ∀ address, start≤address → address<Listing9PackedLayout.endPC mode start transitions nodes → environment.writable address=true)
    (executable : ∀ address, start≤address → address<Listing9PackedLayout.endPC mode start transitions nodes → environment.executable address=true) :
    Mapped mode environment ⟨start,Listing9PackedLayout.endPC mode start transitions nodes⟩ :=
  ⟨fits mode environment.paging start transitions nodes bounds canonical,readable,writable,executable⟩

/-- The final PC is an observation boundary. A strict low-canonical endpoint
is needed because containment of all emitted bytes permits a noncanonical
first byte immediately after the image. No fetch at this endpoint is claimed. -/
theorem endpoint_valid (mode : Mode) (paging : Paging) (start transitions nodes : Nat)
    (bounds : Listing9PackedLayout.Bounds mode start transitions nodes)
    (canonical : mode=.x64 → Listing9PackedLayout.endPC mode start transitions nodes<half paging ∨ highStart paging≤start) :
    Valid mode paging (Listing9PackedLayout.endPC mode start transitions nodes) := by
  have capacity:=bounds.capacity
  have following : start≤Listing9PackedLayout.endPC mode start transitions nodes := by
    rw [Listing9PackedCapacity.endPC_exact]
    omega
  cases mode with
  | x86 => exact capacity
  | x64 =>
    rcases canonical rfl with low | high
    · exact Or.inl low
    · exact Or.inr ⟨Nat.le_trans high following,capacity⟩

end SmcTuring.Appendix.Listing9CanonicalMapping
