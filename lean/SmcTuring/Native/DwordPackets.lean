module
public import SmcTuring.Native.StringMixed
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Native.DwordPackets
abbrev Dword := BitVec 32
inductive Operation where
  | store | bitXor | bitAnd | bitOr | complement
  deriving DecidableEq, Repr
@[expose] def raw : Operation → Dword → DwordArithmetic.Form
  | .store,v => .store 0 v
  | .bitXor,v => .bitXor 0 v
  | .bitAnd,v => .bitAnd 0 v
  | .bitOr,v => .bitOr 0 v
  | .complement,_ => .complement 0
structure Site where
  pc : Nat
  operation : Operation
  target : Nat
  deriving DecidableEq
@[expose] def size (site : Site) := DwordArithmetic.length (raw site.operation 0)
@[expose] def form (mode : Mode) (site : Site) (value : Dword) :=
  DwordArithmetic.located mode (raw site.operation value) site.pc site.target
@[expose] def header (mode : Mode) (site : Site) := (DwordArithmetic.encode (form mode site 0)).take 6
@[expose] def Current (mode : Mode) (site : Site) (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory site.pc 6 = header mode site
@[expose] def live (mode : Mode) (site : Site) (memory : ByteMemory.Memory) := form mode site (DwordCode.get memory (site.pc+6))
@[expose] def Valid (mode : Mode) (site : Site) : Prop :=
  site.pc+size site < 2^(8*mode.wordBytes) ∧ site.target < 2^(8*mode.wordBytes) ∧
    (mode = .x64 → Relocation.SignedDelta (site.pc+size site) site.target)
@[expose] def Contiguous : Nat → List Site → Prop
  | _,[] => True
  | start,site::sites => site.pc = start ∧ Contiguous (site.pc+size site) sites
@[expose] def Intact (mode : Mode) (sites : List Site) (memory : ByteMemory.Memory) : Prop :=
  ∀ site ∈ sites, Current mode site memory
@[expose] def OutsideHeaders (sites : List Site) : Prop :=
  ∀ writer ∈ sites, ∀ reader ∈ sites, writer.target+4 ≤ reader.pc ∨ reader.pc+6 ≤ writer.target
@[expose] def execute (mode : Mode) (site : Site) (state : Execution.State mode) :=
  DwordArithmetic.execute mode (live mode site state.memory) state
@[expose] def finish (mode : Mode) : List Site → Execution.State mode → Execution.State mode
  | [],state => state
  | site::sites,state => finish mode sites (execute mode site state)
@[expose] def program (mode : Mode) : List Site → Execution.State mode → List (StringDword.Form mode)
  | [],_ => []
  | site::sites,state => StringDwordArithmetic.canonical mode (live mode site state.memory)::
      program mode sites (execute mode site state)

/-- Reading a complete DWORD and encoding it returns exactly its live bytes. -/
theorem payload (memory : ByteMemory.Memory) (pc : Nat) :
    ByteMemory.bytesAt memory pc 4 = LittleEndian.wordEncode 4 (DwordCode.get memory pc) := by
  exact (LittleEndian.word_encode_decode 4 _ _ (DwordCode.read_total memory pc)).symm

theorem header_length (mode : Mode) (site : Site) : (header mode site).length = 6 := by
  cases site with
  | mk pc op target => cases op <;> rfl

theorem current (mode : Mode) (site : Site) (memory : ByteMemory.Memory)
    (intact : Current mode site memory) :
    ByteMemory.bytesAt memory site.pc (DwordArithmetic.encode (live mode site memory)).length =
      DwordArithmetic.encode (live mode site memory) := by
  cases site with
  | mk pc op target =>
    cases op
    all_goals try exact intact
    all_goals change ByteMemory.bytesAt memory pc (6+4) = _
    all_goals rw [ByteWindow.append,show ByteMemory.bytesAt memory pc 6 = _ from intact,payload]
    all_goals rfl

theorem initial_header (mode : Mode) (site : Site) (value : Dword) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory site.pc (DwordArithmetic.encode (form mode site value)).length =
      DwordArithmetic.encode (form mode site value)) : Current mode site memory := by
  have length : 6 ≤ (DwordArithmetic.encode (form mode site value)).length := by
    cases site with
    | mk pc op target => cases op <;> simp [form,raw,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.encode]
  rw [Current,←Fetch.bytes_at_take memory site.pc _ 6 length,current]
  cases site with
  | mk pc op target => cases op <;> rfl

theorem effect (mode : Mode) (site : Site) (valid : Valid mode site) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode site.pc) :
    execute mode site state = {state with
      pc := Arithmetic.encodeNat mode (site.pc+size site)
      carry := DwordArithmetic.flag (raw site.operation (DwordCode.get state.memory (site.pc+6)))
        (DwordCode.get state.memory site.target) state.carry
      memory := DwordCode.put state.memory site.target
        (DwordArithmetic.result (raw site.operation (DwordCode.get state.memory (site.pc+6)))
          (DwordCode.get state.memory site.target) state.carry)} := by
  have lengths : DwordArithmetic.length (raw site.operation (DwordCode.get state.memory (site.pc+6))) = size site := by
    cases site with
    | mk pc op target => cases op <;> rfl
  simpa only [execute,live,form,lengths] using DwordArithmetic.located_effect mode
    (raw site.operation (DwordCode.get state.memory (site.pc+6))) site.pc site.target state
    (by cases site with | mk pc op target => cases op <;> rfl) entry
    (by simpa only [lengths] using valid.2.2) valid.2.1

theorem intact_put (mode : Mode) (sites : List Site) (memory : ByteMemory.Memory)
    (intact : Intact mode sites memory) (field : Nat) (value : Dword)
    (outside : ∀ reader ∈ sites, field+4 ≤ reader.pc ∨ reader.pc+6 ≤ field) :
    Intact mode sites (DwordCode.put memory field value) := by
  intro reader member
  rw [Current,DwordMixedImage.bytes_frame _ _ _ _ _ (outside reader member)]
  exact intact reader member

/-- The initial headers and static write separation supply every actual
mutable-payload fetch; the resulting instruction forms read the live bytes. -/
theorem trace (mode : Mode) (sites : List Site) (start : Nat)
    (chain : Contiguous start sites) (valid : ∀ site ∈ sites, Valid mode site)
    (outside : OutsideHeaders sites) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (intact : Intact mode sites state.principal.memory) :
    StringDword.Trace mode state (program mode sites state.principal)
      {state with principal := finish mode sites state.principal} := by
  induction sites generalizing start state with
  | nil => exact .nil state
  | cons site sites ih =>
    have ready := valid site (List.mem_cons_self ..)
    have location : state.principal.pc = Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have fits : site.pc < 2^(8*mode.wordBytes) := by have bound := ready.1;omega
    have fetched : StringDword.fetch mode state.principal.memory state.principal.pc.toNat =
        some (StringDwordArithmetic.canonical mode (live mode site state.principal.memory)) := by
      rw [location,Arithmetic.encode_nat_toNat mode site.pc fits]
      exact StringDwordArithmetic.encoding mode _ _ _ (current mode site _ (intact site (List.mem_cons_self ..)))
    have firstEffect := effect mode site ready state.principal location
    have next : (execute mode site state.principal).pc = Arithmetic.encodeNat mode (site.pc+size site) := by rw [firstEffect]
    have restIntact : Intact mode sites (execute mode site state.principal).memory := by
      rw [firstEffect]
      exact intact_put mode sites state.principal.memory
        (fun reader member => intact reader (List.mem_cons_of_mem _ member)) _ _
        (fun reader member => outside site (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader readerMember => outside writer (List.mem_cons_of_mem _ member)
        reader (List.mem_cons_of_mem _ readerMember)) {state with principal := execute mode site state.principal} next restIntact
    apply StringDword.Trace.step fetched
    rw [StringDwordArithmetic.execute]
    exact rest

theorem instruction_count (mode : Mode) (sites : List Site) (state : Execution.State mode) :
    (program mode sites state).length = sites.length := by
  induction sites generalizing state with
  | nil => rfl
  | cons site sites ih => simp only [program,List.length_cons,ih]


@[expose] def bytes (mode : Mode) (sites : List Site) (value : Dword) :=
  sites.flatMap (fun site => DwordArithmetic.encode (form mode site value))

theorem bytes_length (mode : Mode) (sites : List Site) (value : Dword) :
    (bytes mode sites value).length = (sites.map size).sum := by
  induction sites with
  | nil => rfl
  | cons site sites ih =>
    simp only [bytes,List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons] at *
    rw [ih,DwordArithmetic.encode_length,form,DwordArithmetic.located,DwordArithmetic.relocate_length]
    congr 1
    cases site with | mk pc op target => cases op <;> rfl

theorem initial_headers (mode : Mode) (sites : List Site) (start : Nat) (value : Dword)
    (chain : Contiguous start sites) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory start (bytes mode sites value).length = bytes mode sites value) :
    Intact mode sites memory := by
  induction sites generalizing start with
  | nil => intro site member;cases member
  | cons site sites ih =>
    have first := ByteWindow.packet memory start [] (DwordArithmetic.encode (form mode site value))
      (bytes mode sites value) (by simpa [bytes] using current)
    have rest := ByteWindow.packet memory start (DwordArithmetic.encode (form mode site value))
      (bytes mode sites value) [] (by simpa [bytes,List.append_assoc] using current)
    have length : (DwordArithmetic.encode (form mode site value)).length = size site := by
      rw [DwordArithmetic.encode_length,form,DwordArithmetic.located,DwordArithmetic.relocate_length]
      cases site with | mk pc op target => cases op <;> rfl
    rw [length,←chain.1] at rest
    have later := ih _ chain.2 (by simpa only [List.append_nil] using rest)
    intro reader member
    rcases List.mem_cons.mp member with rfl | member
    · apply initial_header mode _ value memory
      simpa only [List.length_nil,Nat.add_zero,←chain.1] using first
    · exact later reader member

theorem endpoint (mode : Mode) (sites : List Site) (start : Nat)
    (chain : Contiguous start sites) (valid : ∀ site ∈ sites, Valid mode site)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start) :
    (finish mode sites state).pc = Arithmetic.encodeNat mode (start+(sites.map size).sum) := by
  induction sites generalizing start state with
  | nil => simpa only [finish,List.map_nil,List.sum_nil,Nat.add_zero] using entry
  | cons site sites ih =>
    have first := effect mode site (valid site (List.mem_cons_self ..)) state
      (by rw [chain.1];exact entry)
    have next : (execute mode site state).pc = Arithmetic.encodeNat mode (site.pc+size site) := by rw [first]
    change (finish mode sites (execute mode site state)).pc = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next]
    simp only [List.map_cons,List.sum_cons,chain.1,Nat.add_assoc]

theorem window (mode : Mode) (sites : List Site) (start : Nat)
    (chain : Contiguous start sites) (valid : ∀ site ∈ sites, Valid mode site)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start)
    (observed count : Nat) (outside : ∀ site ∈ sites, site.target+4 ≤ observed ∨ observed+count ≤ site.target) :
    ByteMemory.bytesAt (finish mode sites state).memory observed count = ByteMemory.bytesAt state.memory observed count := by
  induction sites generalizing start state with
  | nil => rfl
  | cons site sites ih =>
    have first := effect mode site (valid site (List.mem_cons_self ..)) state
      (by rw [chain.1];exact entry)
    have next : (execute mode site state).pc = Arithmetic.encodeNat mode (site.pc+size site) := by rw [first]
    change ByteMemory.bytesAt (finish mode sites (execute mode site state)).memory observed count = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next
      (fun reader member => outside reader (List.mem_cons_of_mem _ member)),first,
      DwordMixedImage.bytes_frame _ _ _ _ _ (outside site (List.mem_cons_self ..))]

theorem registers (mode : Mode) (sites : List Site) (state : Execution.State mode) :
    (finish mode sites state).accumulator = state.accumulator ∧ (finish mode sites state).stack = state.stack := by
  induction sites generalizing state with
  | nil => exact ⟨rfl,rfl⟩
  | cons site sites ih => exact ih (execute mode site state)

end SmcTuring.Native.DwordPackets
