module
public import SmcTuring.Native.DwordXorHelper

public section
namespace SmcTuring.Native.DwordXorSequence
abbrev Layout := DwordXorHelper.Layout
@[expose] def Contiguous : Nat → List Layout → Prop
  | _,[] => True
  | start,l::ls => l.start = start ∧ Contiguous (DwordXorHelper.endPC l) ls
@[expose] def OutsideCodes (ls : List Layout) : Prop :=
  ∀ writer ∈ ls, ∀ reader ∈ ls, writer.destination+4 ≤ reader.start ∨ DwordXorHelper.endPC reader ≤ writer.destination
@[expose] def bytes (mode : Mode) (ls : List Layout) := ls.flatMap (DwordXorHelper.bytes mode)
@[expose] def program (mode : Mode) (ls : List Layout) := ls.flatMap (DwordXorHelper.program mode)
@[expose] def finish (mode : Mode) (ls : List Layout) (state : StringExecution.State mode) :=
  ls.foldl (fun current l => DwordXorHelper.stringFinish mode l current) state
@[expose] def writes : List Layout → ByteMemory.Memory → ByteMemory.Memory
  | [],memory => memory
  | l::ls,memory => writes ls (DwordCode.put memory l.destination
      (DwordCode.get memory l.destination ^^^ DwordCode.get memory l.source))

@[expose] def Intact (mode : Mode) (ls : List Layout) (memory : ByteMemory.Memory) : Prop :=
  ∀ l ∈ ls, ByteMemory.bytesAt memory l.start 18 = DwordXorHelper.bytes mode l

/-- Initial helper images and static code separation derive every later
fetch, even when different helpers use different pointer halves. -/
theorem trace (mode : Mode) (ls : List Layout) (start : Nat) (chain : Contiguous start ls)
    (valid : ∀ l ∈ ls, DwordXorHelper.Admissible mode l) (outside : OutsideCodes ls)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (intact : Intact mode ls state.principal.memory) :
    StringDword.Trace mode state (program mode ls) (finish mode ls state) := by
  induction ls generalizing start state with
  | nil => exact .nil state
  | cons l ls ih =>
    have location : state.principal.pc = Arithmetic.encodeNat mode l.start := by rw [chain.1];exact entry
    have first := DwordXorHelper.trace mode l (valid l (List.mem_cons_self ..)) state location
      (intact l (List.mem_cons_self ..))
    let nextState := DwordXorHelper.stringFinish mode l state
    have next : nextState.principal.pc = Arithmetic.encodeNat mode (DwordXorHelper.endPC l) := by
      change (DwordXorHelper.finish mode l state.principal).pc = _
      rw [DwordXorHelper.effect mode l (valid l (List.mem_cons_self ..)) state.principal location]
    have kept : Intact mode ls nextState.principal.memory := by
      intro reader member
      change ByteMemory.bytesAt (DwordXorHelper.finish mode l state.principal).memory reader.start 18 = _
      rw [DwordXorHelper.window mode l (valid l (List.mem_cons_self ..)) state.principal location reader.start 18
        (outside l (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))]
      exact intact reader (List.mem_cons_of_mem _ member)
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader readerMember => outside writer (List.mem_cons_of_mem _ member) reader (List.mem_cons_of_mem _ readerMember)) nextState next kept
    simpa only [program,List.flatMap_cons,finish,List.foldl_cons,nextState] using StringDword.trace_append mode first rest

theorem initial_helpers (mode : Mode) (ls : List Layout) (start : Nat) (chain : Contiguous start ls)
    (memory : ByteMemory.Memory) (current : ByteMemory.bytesAt memory start (bytes mode ls).length = bytes mode ls) :
    Intact mode ls memory := by
  induction ls generalizing start with
  | nil => intro l member;cases member
  | cons l ls ih =>
    have first := ByteWindow.packet memory start [] (DwordXorHelper.bytes mode l) (bytes mode ls) (by simpa [bytes] using current)
    have rest := ByteWindow.packet memory start (DwordXorHelper.bytes mode l) (bytes mode ls) [] (by simpa [bytes,List.append_assoc] using current)
    rw [DwordXorHelper.bytes_length,←chain.1] at rest
    have later := ih _ chain.2 (by simpa only [DwordXorHelper.endPC,List.append_nil] using rest)
    intro reader member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [DwordXorHelper.bytes_length,List.length_nil,Nat.add_zero,←chain.1] using first
    · exact later reader member

theorem endpoint (mode : Mode) (ls : List Layout) (start : Nat) (chain : Contiguous start ls)
    (valid : ∀ l ∈ ls, DwordXorHelper.Admissible mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (finish mode ls state).principal.pc = Arithmetic.encodeNat mode (start+ls.length*18) := by
  induction ls generalizing start state with
  | nil => simpa [finish] using entry
  | cons l ls ih =>
    have effect := DwordXorHelper.effect mode l (valid l (List.mem_cons_self ..)) state.principal
      (by rw [chain.1];exact entry)
    have next : (DwordXorHelper.stringFinish mode l state).principal.pc = Arithmetic.encodeNat mode (DwordXorHelper.endPC l) := by
      change (DwordXorHelper.finish mode l state.principal).pc = _
      rw [effect]
    change (finish mode ls (DwordXorHelper.stringFinish mode l state)).principal.pc = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next]
    congr 1
    simp [DwordXorHelper.endPC,chain.1,List.length_cons,Nat.add_mul,Nat.add_assoc] <;> omega

theorem memory_effect (mode : Mode) (ls : List Layout) (start : Nat) (chain : Contiguous start ls)
    (valid : ∀ l ∈ ls, DwordXorHelper.Admissible mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (finish mode ls state).principal.memory = writes ls state.principal.memory := by
  induction ls generalizing start state with
  | nil => rfl
  | cons l ls ih =>
    have effect := DwordXorHelper.effect mode l (valid l (List.mem_cons_self ..)) state.principal
      (by rw [chain.1];exact entry)
    have next : (DwordXorHelper.stringFinish mode l state).principal.pc = Arithmetic.encodeNat mode (DwordXorHelper.endPC l) := by
      change (DwordXorHelper.finish mode l state.principal).pc = _
      rw [effect]
    change (finish mode ls (DwordXorHelper.stringFinish mode l state)).principal.memory = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next]
    change writes ls (DwordXorHelper.finish mode l state.principal).memory = _
    rw [effect]
    rfl


theorem window (mode : Mode) (ls : List Layout) (start : Nat) (chain : Contiguous start ls)
    (valid : ∀ l ∈ ls, DwordXorHelper.Admissible mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (observed count : Nat) (outside : ∀ l ∈ ls, l.destination+4 ≤ observed ∨ observed+count ≤ l.destination) :
    ByteMemory.bytesAt (finish mode ls state).principal.memory observed count = ByteMemory.bytesAt state.principal.memory observed count := by
  induction ls generalizing start state with
  | nil => rfl
  | cons l ls ih =>
    have effect := DwordXorHelper.effect mode l (valid l (List.mem_cons_self ..)) state.principal
      (by rw [chain.1];exact entry)
    have next : (DwordXorHelper.stringFinish mode l state).principal.pc = Arithmetic.encodeNat mode (DwordXorHelper.endPC l) := by
      change (DwordXorHelper.finish mode l state.principal).pc = _
      rw [effect]
    change ByteMemory.bytesAt (finish mode ls (DwordXorHelper.stringFinish mode l state)).principal.memory observed count = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next
      (fun reader member => outside reader (List.mem_cons_of_mem _ member))]
    change ByteMemory.bytesAt (DwordXorHelper.finish mode l state.principal).memory observed count = _
    exact DwordXorHelper.window mode l (valid l (List.mem_cons_self ..)) state.principal
      (by rw [chain.1];exact entry) observed count (outside l (List.mem_cons_self ..))

theorem instruction_count (mode : Mode) (ls : List Layout) : (program mode ls).length = ls.length*3 := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [program,List.flatMap_cons,List.length_append,DwordXorHelper.program,
      List.length_cons,List.length_nil] at ih ⊢
    omega

theorem registers (mode : Mode) (ls : List Layout) (start : Nat) (chain : Contiguous start ls)
    (valid : ∀ l ∈ ls, DwordXorHelper.Admissible mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (finish mode ls state).principal.stack = state.principal.stack ∧
    (finish mode ls state).principal.carry = (if ls.length = 0 then state.principal.carry else false) ∧
    (finish mode ls state).principal.accumulator =
      (if ls.length = 0 then state.principal.accumulator else DwordCode.lift mode (DwordCode.low mode state.principal.accumulator)) ∧
    (finish mode ls state).sourceIndex = state.sourceIndex ∧
    (finish mode ls state).destinationIndex = state.destinationIndex ∧
    (finish mode ls state).backwards = state.backwards := by
  induction ls generalizing start state with
  | nil => simp [finish]
  | cons l ls ih =>
    have first := DwordXorHelper.effect mode l (valid l (List.mem_cons_self ..)) state.principal
      (by rw [chain.1];exact entry)
    have next : (DwordXorHelper.stringFinish mode l state).principal.pc = Arithmetic.encodeNat mode (DwordXorHelper.endPC l) := by
      change (DwordXorHelper.finish mode l state.principal).pc = _
      rw [first]
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next
    simpa only [finish,List.foldl_cons,DwordXorHelper.stringFinish,first,List.length_cons,
      Nat.succ_ne_zero,ite_false,DwordCode.low_lift,ite_self] using rest

end SmcTuring.Native.DwordXorSequence
