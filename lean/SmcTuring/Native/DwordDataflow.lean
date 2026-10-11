module
public import SmcTuring.Native.DwordPackets
public import SmcTuring.Native.StringDwordSequence

public section
namespace SmcTuring.Native.DwordDataflow
abbrev Dword := BitVec 32
@[expose] def helperMemory : List DwordLayout.Layout → ByteMemory.Memory → ByteMemory.Memory
  | [],memory => memory
  | layout::layouts,memory => helperMemory layouts
      (DwordCode.put memory layout.destination (DwordCode.get memory layout.source))
@[expose] def packetMemory : List DwordPackets.Site → ByteMemory.Memory → ByteMemory.Memory
  | [],memory => memory
  | site::sites,memory => packetMemory sites
      (DwordCode.put memory site.target (DwordArithmetic.result
        (DwordPackets.raw site.operation (DwordCode.get memory (site.pc+6)))
        (DwordCode.get memory site.target) false))

theorem no_carry (operation : DwordPackets.Operation) (payload old : Dword) (cf : Bool) :
    DwordArithmetic.result (DwordPackets.raw operation payload) old cf =
      DwordArithmetic.result (DwordPackets.raw operation payload) old false := by cases operation <;> rfl

/-- Exact helper memory follows current source reads, including a source
populated by an earlier helper. The actual PC/effect proof supplies the link. -/
theorem helpers (mode : Mode) (layouts : List DwordLayout.Layout) (start : Nat)
    (chain : StringDwordSequence.Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (StringDwordSequence.finish mode layouts state).principal.memory = helperMemory layouts state.principal.memory := by
  induction layouts generalizing start state with
  | nil => rfl
  | cons layout layouts ih =>
    have effect := DwordEffects.effect mode layout (valid layout (List.mem_cons_self ..)) state.principal
      (by rw [chain.1];exact entry)
    have next : (StringDwordCopy.dwordFinish mode layout state).principal.pc =
        Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      change (DwordEffects.finish mode layout state.principal).pc = _
      rw [effect]
    change (StringDwordSequence.finish mode layouts (StringDwordCopy.dwordFinish mode layout state)).principal.memory = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next]
    change helperMemory layouts (DwordEffects.finish mode layout state.principal).memory = _
    rw [effect]
    rfl

/-- The printed Boolean/store packets have no CF-dependent memory result.
Their dynamically fetched payloads determine these exact memory effects. -/
theorem packets (mode : Mode) (sites : List DwordPackets.Site) (start : Nat)
    (chain : DwordPackets.Contiguous start sites) (valid : ∀ site ∈ sites, DwordPackets.Valid mode site)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start) :
    (DwordPackets.finish mode sites state).memory = packetMemory sites state.memory := by
  induction sites generalizing start state with
  | nil => rfl
  | cons site sites ih =>
    have effect := DwordPackets.effect mode site (valid site (List.mem_cons_self ..)) state
      (by rw [chain.1];exact entry)
    have next : (DwordPackets.execute mode site state).pc = Arithmetic.encodeNat mode (site.pc+DwordPackets.size site) := by rw [effect]
    change (DwordPackets.finish mode sites (DwordPackets.execute mode site state)).memory = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next,effect,no_carry]
    rfl

/-- Complete DWORD reads at separated offsets preserve their original value. -/
theorem read_offset (memory : ByteMemory.Memory) (base written observed : Nat) (value : Dword)
    (separate : written+4 ≤ observed ∨ observed+4 ≤ written) :
    DwordCode.get (DwordCode.put memory (base+written) value) (base+observed) =
      DwordCode.get memory (base+observed) := by
  apply DwordCode.get_frame
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases separate with before | after <;> omega


theorem word_frame (mode : Mode) (memory : ByteMemory.Memory) (pc observed : Nat) (value : Word mode)
    (outside : pc+mode.wordBytes ≤ observed ∨ observed+4 ≤ pc) :
    DwordCode.get (ByteMemory.putWord mode memory pc value) observed = DwordCode.get memory observed := by
  have window := ByteMemory.bytes_at_frame memory pc (LittleEndian.wordEncode mode.wordBytes value) observed 4 (by
    intro index
    have bound := index.isLt
    simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
    rcases outside with before | after <;> omega)
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) window

theorem read_disjoint (memory : ByteMemory.Memory) (written observed : Nat) (value : Dword)
    (separate : written+4 ≤ observed ∨ observed+4 ≤ written) :
    DwordCode.get (DwordCode.put memory written value) observed = DwordCode.get memory observed := by
  apply DwordCode.get_frame
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases separate with before | after <;> omega

end SmcTuring.Native.DwordDataflow
