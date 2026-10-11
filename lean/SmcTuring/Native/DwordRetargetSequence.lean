module
public import SmcTuring.Native.DwordRetarget
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Native.DwordRetargetSequence
open LittleEndian

structure Site where
  pc : Nat
  owner : Nat
  destination : Nat
  deriving DecidableEq

@[expose] def Contiguous : Nat → List Site → Prop
  | _, [] => True
  | start, site::sites => site.pc = start ∧ Contiguous (site.pc+10) sites
@[expose] def Valid (mode : Mode) (site : Site) : Prop :=
  site.pc+10 < 2^(8*mode.wordBytes) ∧ site.owner+6 < 2^(8*mode.wordBytes) ∧
    (mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
@[expose] def form (mode : Mode) (site : Site) := DwordRetarget.patchForm mode site.pc site.owner site.destination
@[expose] def Intact (mode : Mode) (sites : List Site) (memory : ByteMemory.Memory) : Prop :=
  ∀ site ∈ sites, ByteMemory.bytesAt memory site.pc 10 = DwordArithmetic.encode (form mode site)
@[expose] def OutsideCodes (sites : List Site) : Prop :=
  ∀ writer ∈ sites, ∀ reader ∈ sites,
    writer.owner+6 ≤ reader.pc ∨ reader.pc+10 ≤ writer.owner+2
@[expose] def program (mode : Mode) (sites : List Site) : List (MixedDword.Form mode) :=
  sites.map (fun site => MixedDword.Form.arithmetic (form mode site))
@[expose] def bytes (mode : Mode) (sites : List Site) := sites.flatMap (fun site => DwordArithmetic.encode (form mode site))
@[expose] def finish (mode : Mode) (sites : List Site) (state : Execution.State mode) :=
  sites.foldl (fun current site => DwordRetarget.patched mode site.pc site.owner site.destination current) state
@[expose] def writes (mode : Mode) (sites : List Site) (memory : ByteMemory.Memory) :=
  sites.foldl (fun current site => DwordCode.put current (site.owner+2)
    (DwordRetarget.printed mode site.pc site.owner site.destination)) memory

theorem bytes_length (mode : Mode) (sites : List Site) : (bytes mode sites).length = sites.length*10 := by
  induction sites with
  | nil => rfl
  | cons site sites ih =>
    simp only [bytes,List.flatMap_cons,List.length_append,DwordArithmetic.encode_length,form,
      DwordRetarget.patchForm,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,List.length_cons] at *
    omega

theorem bytes_frame (memory : ByteMemory.Memory) (site : Site) (value : BitVec 32) (start count : Nat)
    (outside : site.owner+6 ≤ start ∨ start+count ≤ site.owner+2) :
    ByteMemory.bytesAt (DwordCode.put memory (site.owner+2) value) start count = ByteMemory.bytesAt memory start count := by
  apply ByteMemory.bytes_at_frame
  intro index
  have bound := index.isLt
  simp only [word_encode_length,ByteMemory.Inside]
  rcases outside with before | after <;> omega

theorem intact_of_bytes (mode : Mode) (sites : List Site) (start : Nat)
    (chain : Contiguous start sites) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory start (bytes mode sites).length = bytes mode sites) :
    Intact mode sites memory := by
  induction sites generalizing start with
  | nil => intro site member; cases member
  | cons site sites ih =>
    have first := ByteWindow.packet memory start [] (DwordArithmetic.encode (form mode site))
      (bytes mode sites) (by simpa [bytes] using current)
    have rest := ByteWindow.packet memory start (DwordArithmetic.encode (form mode site)) (bytes mode sites) []
      (by simpa [bytes,List.append_assoc] using current)
    have length : (DwordArithmetic.encode (form mode site)).length = 10 := rfl
    rw [length,←chain.1] at rest
    have later := ih _ chain.2 (by simpa only [List.append_nil] using rest)
    intro reader member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [List.length_nil,Nat.add_zero,length,←chain.1] using first
    · exact later reader member

theorem trace (mode : Mode) (sites : List Site) (start : Nat) (chain : Contiguous start sites)
    (valid : ∀ site ∈ sites, Valid mode site) (outside : OutsideCodes sites)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start)
    (intact : Intact mode sites state.memory) :
    MixedDword.Trace mode state (program mode sites) (finish mode sites state) := by
  induction sites generalizing start state with
  | nil => exact .nil state
  | cons site sites ih =>
    have ready := valid site (List.mem_cons_self ..)
    have codeFits := ready.1
    have ownerFits := ready.2.1
    have location : state.pc = Arithmetic.encodeNat mode site.pc := by rw [chain.1]; exact entry
    have first := DwordRetarget.patch_trace mode site.pc site.owner site.destination state location
      (by omega) (intact site (List.mem_cons_self ..))
    have effect := DwordRetarget.patch_effect mode site.pc site.owner site.destination state location ready.2.2 (by omega)
    have next : (DwordRetarget.patched mode site.pc site.owner site.destination state).pc =
        Arithmetic.encodeNat mode (site.pc+10) := by rw [effect]
    have restIntact : Intact mode sites (DwordRetarget.patched mode site.pc site.owner site.destination state).memory := by
      intro reader member
      rw [effect,bytes_frame _ site _ reader.pc 10
        (outside site (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))]
      exact intact reader (List.mem_cons_of_mem _ member)
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader readerMember => outside writer (List.mem_cons_of_mem _ member)
        reader (List.mem_cons_of_mem _ readerMember)) _ next restIntact
    simpa only [program,List.map_cons,finish,List.foldl_cons,List.cons_append,List.nil_append,form]
      using MixedDword.trace_append mode first rest

theorem effect (mode : Mode) (sites : List Site) (start : Nat) (chain : Contiguous start sites)
    (valid : ∀ site ∈ sites, Valid mode site) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode start) :
    finish mode sites state = { state with
      pc := Arithmetic.encodeNat mode (start+sites.length*10)
      memory := writes mode sites state.memory } := by
  induction sites generalizing start state with
  | nil => simp only [finish,writes,List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero,←entry]
  | cons site sites ih =>
    have ready := valid site (List.mem_cons_self ..)
    have ownerFits := ready.2.1
    have location : state.pc = Arithmetic.encodeNat mode site.pc := by rw [chain.1]; exact entry
    have first := DwordRetarget.patch_effect mode site.pc site.owner site.destination state location ready.2.2 (by omega)
    have next : (DwordRetarget.patched mode site.pc site.owner site.destination state).pc =
        Arithmetic.encodeNat mode (site.pc+10) := by rw [first]
    change finish mode sites (DwordRetarget.patched mode site.pc site.owner site.destination state) = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next,first]
    simp only [writes,List.foldl_cons,List.length_cons]
    have endpoint : site.pc+10+sites.length*10 = start+(sites.length+1)*10 := by rw [chain.1]; omega
    rw [endpoint]

theorem writes_window (mode : Mode) (sites : List Site) (memory : ByteMemory.Memory) (start count : Nat)
    (outside : ∀ site ∈ sites, site.owner+6 ≤ start ∨ start+count ≤ site.owner+2) :
    ByteMemory.bytesAt (writes mode sites memory) start count = ByteMemory.bytesAt memory start count := by
  induction sites generalizing memory with
  | nil => rfl
  | cons site sites ih =>
    change ByteMemory.bytesAt (writes mode sites (DwordCode.put memory (site.owner+2) _)) start count = _
    rw [ih _ (fun reader member => outside reader (List.mem_cons_of_mem _ member)),
      bytes_frame _ site _ start count (outside site (List.mem_cons_self ..))]

/-- Each selected owner receives its new displacement while its complete
header and live immediate are retained; other sites have disjoint footprints.
This applies to a copied owner with any old address bytes. -/
theorem owner_current (mode : Mode) (sites : List Site) (nodup : sites.Nodup) (reader : Site)
    (member : reader ∈ sites) (memory : ByteMemory.Memory) (old value : BitVec 32)
    (current : ByteMemory.bytesAt memory reader.owner 10 = DwordArithmetic.encode (.store old value))
    (outside : ∀ writer ∈ sites, writer ≠ reader →
      writer.owner+6 ≤ reader.owner ∨ reader.owner+10 ≤ writer.owner+2) :
    ByteMemory.bytesAt (writes mode sites memory) reader.owner 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode reader.owner (reader.destination+6) value) := by
  induction sites generalizing memory with
  | nil => cases member
  | cons site sites ih =>
    change ByteMemory.bytesAt (writes mode sites (DwordCode.put memory (site.owner+2) _)) reader.owner 10 = _
    rcases List.mem_cons.mp member with same | tailMember
    · subst site
      rw [writes_window mode sites _ reader.owner 10 (by
        intro writer member
        apply outside writer (List.mem_cons_of_mem _ member)
        intro same
        subst writer
        exact (List.nodup_cons.mp nodup).1 member)]
      have patched := DwordRetarget.displacement_patch memory reader.owner old
        (DwordRetarget.printed mode reader.pc reader.owner reader.destination) value current
      simpa only [DwordRetarget.printed_displacement,DwordRetarget.ownerForm,
        DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length] using patched
    · have different : site ≠ reader := by
        intro same
        subst site
        exact (List.nodup_cons.mp nodup).1 tailMember
      have later : ByteMemory.bytesAt (DwordCode.put memory (site.owner+2)
          (DwordRetarget.printed mode site.pc site.owner site.destination)) reader.owner 10 =
          DwordArithmetic.encode (.store old value) := by
        rw [bytes_frame _ site _ reader.owner 10 (outside site (List.mem_cons_self ..) different)]
        exact current
      exact ih (List.nodup_cons.mp nodup).2 tailMember _ later
        (fun writer member different => outside writer (List.mem_cons_of_mem _ member) different)

/-- Actual current PCs resolve every four-byte write into the statically
specified owner field; ownership is propagated through the executed states. -/
theorem owned_run (mode : Mode) (sites : List Site) (start : Nat) (chain : Contiguous start sites)
    (valid : ∀ site ∈ sites, Valid mode site) (owned : Nat → Nat → Prop)
    (fields : ∀ site ∈ sites, owned (site.owner+2) 4)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start) :
    MixedDword.OwnedRun mode owned (program mode sites) state := by
  induction sites generalizing start state with
  | nil => trivial
  | cons site sites ih =>
    have ready := valid site (List.mem_cons_self ..)
    have ownerFits := ready.2.1
    have location : state.pc = Arithmetic.encodeNat mode site.pc := by rw [chain.1]; exact entry
    have address := DwordArithmetic.located_address mode
      (.store 0 (DwordRetarget.printed mode site.pc site.owner site.destination)) site.pc (site.owner+2)
      state rfl location ready.2.2
    have exactAddress : (DwordArithmetic.address mode (form mode site) state).toNat = site.owner+2 := by
      unfold form DwordRetarget.patchForm
      rw [address,Arithmetic.encode_nat_toNat mode _ (by omega)]
    have next : (DwordRetarget.patched mode site.pc site.owner site.destination state).pc =
        Arithmetic.encodeNat mode (site.pc+10) := by
      rw [DwordRetarget.patch_effect mode site.pc site.owner site.destination state location ready.2.2 (by omega)]
    change owned (DwordArithmetic.address mode (form mode site) state).toNat 4 ∧ _
    rw [exactAddress]
    exact ⟨fields site (List.mem_cons_self ..),ih _ chain.2
      (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun reader member => fields reader (List.mem_cons_of_mem _ member)) _ next⟩

end SmcTuring.Native.DwordRetargetSequence
