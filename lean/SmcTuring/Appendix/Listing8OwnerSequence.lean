module
public import SmcTuring.Appendix.Listing8CopiedPointer
public import SmcTuring.Appendix.Listing8CopyImage

public section
namespace SmcTuring.Appendix.Listing8OwnerSequence
open Native Listing8Prototypes

inductive Owner (mode : Mode) where
  | pointer (source pc : Nat) (value : Word mode)
  | scalar (pc target : Nat) (value : BitVec 32)

@[expose] def pc (mode : Mode) : Owner mode → Nat
  | .pointer _ pc _ => pc
  | .scalar pc _ _ => pc
@[expose] def span (mode : Mode) : Owner mode → Nat
  | .pointer _ _ _ => pointerSpan mode
  | .scalar _ _ _ => 10
@[expose] def windows (mode : Mode) : Owner mode → List (Nat × Nat)
  | .pointer source pc value => [(source,(pointerBytes mode source value).length),(pc,(pointerBytes mode source value).length)]
  | .scalar pc _ _ => [(pc,10)]
@[expose] def Current (mode : Mode) (owner : Owner mode) (memory : ByteMemory.Memory) : Prop :=
  match owner with
  | .pointer source pc value =>
      ByteMemory.bytesAt memory source (pointerBytes mode source value).length = pointerBytes mode source value ∧
      ByteMemory.bytesAt memory pc (pointerBytes mode source value).length = pointerBytes mode source value
  | .scalar pc target value => ByteMemory.bytesAt memory pc 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode pc target value)
@[expose] def Valid (mode : Mode) : Owner mode → Prop
  | .pointer source pc value => source+pointerSpan mode < 2^(8*mode.wordBytes) ∧
      pc+pointerSpan mode < 2^(8*mode.wordBytes) ∧
      (source+pointerSpan mode ≤ pc ∨ pc+pointerSpan mode ≤ source) ∧
      (value.toNat+mode.wordBytes ≤ pc ∨ pc+pointerSpan mode ≤ value.toNat) ∧
      value.toNat+mode.wordBytes < 2^(8*mode.wordBytes)
  | .scalar pc target _ => pc+10 < 2^(8*mode.wordBytes) ∧ target+4 < 2^(8*mode.wordBytes) ∧
      (mode = .x64 → Relocation.SignedDelta (pc+10) target)
@[expose] def forms (mode : Mode) : Owner mode → List (StringDword.Form mode)
  | .pointer source pc value => (Listing8CopiedPointer.forms mode source pc value).map StringDword.Form.string
  | .scalar pc target value => [StringDword.store mode (Relocation.memoryDisp mode (pc+10) target) value]
@[expose] def advance (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode) :=
  match owner with
  | .pointer source pc value => Listing8CopiedPointer.finish mode source pc value state
  | .scalar pc target value => StringDword.execute mode (StringDword.store mode (Relocation.memoryDisp mode (pc+10) target) value) state
@[expose] def Contiguous (mode : Mode) : Nat → List (Owner mode) → Prop
  | _, [] => True
  | start, owner::owners => pc mode owner = start ∧ Contiguous mode (pc mode owner+span mode owner) owners
@[expose] def Intact (mode : Mode) (owners : List (Owner mode)) (memory : ByteMemory.Memory) : Prop :=
  ∀ owner ∈ owners, Current mode owner memory
@[expose] def Outside (mode : Mode) (writer reader : Owner mode) : Prop :=
  match writer with
  | .pointer _ _ _ => True
  | .scalar _ target _ => ∀ window ∈ windows mode reader, target+4 ≤ window.1 ∨ window.1+window.2 ≤ target
@[expose] def program (mode : Mode) (owners : List (Owner mode)) := owners.flatMap (forms mode)
@[expose] def finish (mode : Mode) (owners : List (Owner mode)) (state : StringExecution.State mode) :=
  owners.foldl (fun state owner => advance mode owner state) state

theorem scalar_effect (mode : Mode) (pc target : Nat) (value : BitVec 32) (state : StringExecution.State mode)
    (valid : Valid mode (.scalar pc target value)) (entry : state.principal.pc = Arithmetic.encodeNat mode pc) :
    advance mode (.scalar pc target value) state = { state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (pc+10), memory := DwordCode.put state.principal.memory target value} } := by
  rw [advance,StringDword.store_execute]
  have targetFits : target < 2^(8*mode.wordBytes) := by have bound := valid.2.1;omega
  have effect := DwordArithmetic.located_effect mode (.store 0 value) pc target state.principal rfl entry valid.2.2 targetFits
  change DwordArithmetic.execute mode (.store (Relocation.memoryDisp mode (pc+10) target) value) state.principal = _ at effect
  rw [effect]
  rfl

theorem pointer_effect (mode : Mode) (source pc : Nat) (value : Word mode) (state : StringExecution.State mode)
    (valid : Valid mode (.pointer source pc value)) (entry : state.principal.pc = Arithmetic.encodeNat mode pc)
    (current : Current mode (.pointer source pc value) state.principal.memory) :
    advance mode (.pointer source pc value) state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (pc+pointerSpan mode),accumulator := Execution.load mode state.principal.memory value} } :=
  Listing8CopiedPointer.effect mode source pc value state entry
    (Listing8CopiedPointer.self_value mode source pc value _ valid.1 valid.2.1 current.1 current.2)

theorem advance_pc (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode owner) (entry : state.principal.pc = Arithmetic.encodeNat mode (pc mode owner))
    (current : Current mode owner state.principal.memory) :
    (advance mode owner state).principal.pc = Arithmetic.encodeNat mode (pc mode owner+span mode owner) := by
  cases owner with
  | pointer source pc value => rw [pointer_effect mode source pc value state valid entry current];rfl
  | scalar pc target value => rw [scalar_effect mode pc target value state valid entry];rfl

theorem advance_trace (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode owner) (entry : state.principal.pc = Arithmetic.encodeNat mode (pc mode owner))
    (current : Current mode owner state.principal.memory) :
    StringDword.Trace mode state (forms mode owner) (advance mode owner state) := by
  cases owner with
  | pointer source pc value =>
    exact Listing8CopiedPointer.unified_trace mode source pc value state entry valid.1 valid.2.1 valid.2.2.1 valid.2.2.2.1 current.1 current.2
  | scalar pc target value =>
    have startFits : pc < 2^(8*mode.wordBytes) := by have bound := valid.1;omega
    refine .step ?_ (.nil _)
    change state.principal.pc = Arithmetic.encodeNat mode pc at entry
    rw [entry,Arithmetic.encode_nat_toNat mode pc startFits]
    exact StringDword.store_encoding mode _ _ _ _ current

theorem window_frame (mode : Mode) (writer : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode writer) (entry : state.principal.pc = Arithmetic.encodeNat mode (pc mode writer))
    (current : Current mode writer state.principal.memory) (start count : Nat)
    (outside : match writer with | .pointer _ _ _ => True | .scalar _ target _ => target+4 ≤ start ∨ start+count ≤ target) :
    ByteMemory.bytesAt (advance mode writer state).principal.memory start count = ByteMemory.bytesAt state.principal.memory start count := by
  cases writer with
  | pointer source pc value => rw [pointer_effect mode source pc value state valid entry current]
  | scalar pc target value =>
    rw [scalar_effect mode pc target value state valid entry]
    exact Listing8CopyImage.byte_frame _ target (LittleEndian.wordEncode 4 value) start count (by simpa only [LittleEndian.word_encode_length] using outside)

theorem retained (mode : Mode) (writer reader : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode writer) (entry : state.principal.pc = Arithmetic.encodeNat mode (pc mode writer))
    (current : Current mode writer state.principal.memory) (old : Current mode reader state.principal.memory)
    (outside : Outside mode writer reader) : Current mode reader (advance mode writer state).principal.memory := by
  have frame : ∀ window ∈ windows mode reader,
      ByteMemory.bytesAt (advance mode writer state).principal.memory window.1 window.2 = ByteMemory.bytesAt state.principal.memory window.1 window.2 := by
    intro window member
    apply window_frame mode writer state valid entry current
    cases writer with
    | pointer => trivial
    | scalar pc target value => exact outside window member
  cases reader with
  | pointer source pc value =>
    constructor
    · rw [show ByteMemory.bytesAt (advance mode writer state).principal.memory source (pointerBytes mode source value).length =
          ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length from frame (source,(pointerBytes mode source value).length) (by simp [windows])]
      exact old.1
    · rw [show ByteMemory.bytesAt (advance mode writer state).principal.memory pc (pointerBytes mode source value).length =
          ByteMemory.bytesAt state.principal.memory pc (pointerBytes mode source value).length from frame (pc,(pointerBytes mode source value).length) (by simp [windows])]
      exact old.2
  | scalar pc target value =>
    change ByteMemory.bytesAt (advance mode writer state).principal.memory pc 10 = _
    rw [frame (pc,10) (by simp [windows])]
    exact old

/-- Each future packet and original self-field window is retained by the
preceding actual effects. The hypotheses describe only initial bytes and
static placement/relocations, never a future trace or readiness. -/
theorem trace (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner ∈ owners, Valid mode owner)
    (outside : ∀ writer ∈ owners, ∀ reader ∈ owners, Outside mode writer reader)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    StringDword.Trace mode state (program mode owners) (finish mode owners state) := by
  induction owners generalizing start state with
  | nil => exact .nil _
  | cons owner owners ih =>
    have v := valid owner (List.mem_cons_self ..)
    have c := current owner (List.mem_cons_self ..)
    have location : state.principal.pc = Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have first := advance_trace mode owner state v location c
    have next := advance_pc mode owner state v location c
    have restCurrent : Intact mode owners (advance mode owner state).principal.memory := by
      intro reader member
      exact retained mode owner reader state v location c (current reader (List.mem_cons_of_mem _ member))
        (outside owner (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer wm reader rm => outside writer (List.mem_cons_of_mem _ wm) reader (List.mem_cons_of_mem _ rm)) _ next restCurrent
    simpa only [program,List.flatMap_cons,finish,List.foldl_cons] using StringDword.trace_append mode first rest

@[expose] def write (mode : Mode) (owner : Owner mode) (memory : ByteMemory.Memory) :=
  match owner with
  | .pointer _ _ _ => memory
  | .scalar _ target value => DwordCode.put memory target value
@[expose] def writes (mode : Mode) : List (Owner mode) → ByteMemory.Memory → ByteMemory.Memory
  | [], memory => memory
  | owner::owners, memory => writes mode owners (write mode owner memory)
@[expose] def total (mode : Mode) : List (Owner mode) → Nat
  | [] => 0
  | owner::owners => span mode owner+total mode owners

theorem advance_result (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode owner) (entry : state.principal.pc = Arithmetic.encodeNat mode (pc mode owner))
    (current : Current mode owner state.principal.memory) :
    (advance mode owner state).principal.memory = write mode owner state.principal.memory ∧
    (advance mode owner state).principal.stack = state.principal.stack ∧
    (advance mode owner state).principal.carry = state.principal.carry ∧
    (advance mode owner state).sourceIndex = state.sourceIndex ∧
    (advance mode owner state).destinationIndex = state.destinationIndex ∧
    (advance mode owner state).backwards = state.backwards := by
  cases owner with
  | pointer source pc value => rw [pointer_effect mode source pc value state valid entry current]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | scalar pc target value => rw [scalar_effect mode pc target value state valid entry];exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem result (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner ∈ owners, Valid mode owner)
    (outside : ∀ writer ∈ owners, ∀ reader ∈ owners, Outside mode writer reader)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    (finish mode owners state).principal.pc = Arithmetic.encodeNat mode (start+total mode owners) ∧
    (finish mode owners state).principal.memory = writes mode owners state.principal.memory ∧
    (finish mode owners state).principal.stack = state.principal.stack ∧
    (finish mode owners state).principal.carry = state.principal.carry ∧
    (finish mode owners state).sourceIndex = state.sourceIndex ∧
    (finish mode owners state).destinationIndex = state.destinationIndex ∧
    (finish mode owners state).backwards = state.backwards := by
  induction owners generalizing start state with
  | nil => exact ⟨by simpa only [finish,List.foldl_nil,total,Nat.add_zero] using entry,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | cons owner owners ih =>
    have v := valid owner (List.mem_cons_self ..)
    have c := current owner (List.mem_cons_self ..)
    have location : state.principal.pc = Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have next := advance_pc mode owner state v location c
    have first := advance_result mode owner state v location c
    have restCurrent : Intact mode owners (advance mode owner state).principal.memory := by
      intro reader member
      exact retained mode owner reader state v location c (current reader (List.mem_cons_of_mem _ member))
        (outside owner (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer wm reader rm => outside writer (List.mem_cons_of_mem _ wm) reader (List.mem_cons_of_mem _ rm)) _ next restCurrent
    change (finish mode owners (advance mode owner state)).principal.pc = _ ∧ _
    refine ⟨?_,?_,rest.2.2.1.trans first.2.1,rest.2.2.2.1.trans first.2.2.1,
      rest.2.2.2.2.1.trans first.2.2.2.1,rest.2.2.2.2.2.1.trans first.2.2.2.2.1,rest.2.2.2.2.2.2.trans first.2.2.2.2.2⟩
    · simpa only [total,chain.1,Nat.add_assoc] using rest.1
    · exact rest.2.1.trans (congrArg (writes mode owners) first.1)

theorem retained_observer (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner ∈ owners, Valid mode owner)
    (outside : ∀ writer ∈ owners, ∀ reader ∈ owners, Outside mode writer reader)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) (observer : Owner mode)
    (old : Current mode observer state.principal.memory) (observerOutside : ∀ writer ∈ owners, Outside mode writer observer) :
    Current mode observer (finish mode owners state).principal.memory := by
  induction owners generalizing start state with
  | nil => exact old
  | cons owner owners ih =>
    have v := valid owner (List.mem_cons_self ..)
    have c := current owner (List.mem_cons_self ..)
    have location : state.principal.pc = Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have next := advance_pc mode owner state v location c
    have kept := retained mode owner observer state v location c old (observerOutside owner (List.mem_cons_self ..))
    have restCurrent : Intact mode owners (advance mode owner state).principal.memory := by
      intro reader member
      exact retained mode owner reader state v location c (current reader (List.mem_cons_of_mem _ member))
        (outside owner (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))
    exact ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer wm reader rm => outside writer (List.mem_cons_of_mem _ wm) reader (List.mem_cons_of_mem _ rm)) _ next restCurrent kept
      (fun writer wm => observerOutside writer (List.mem_cons_of_mem _ wm))

theorem retained_image (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner ∈ owners, Valid mode owner)
    (outside : ∀ writer ∈ owners, ∀ reader ∈ owners, Outside mode writer reader)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    Intact mode owners (finish mode owners state).principal.memory := by
  intro observer member
  exact retained_observer mode owners start chain valid outside state entry current observer (current observer member)
    (fun writer wm => outside writer wm observer member)

end SmcTuring.Appendix.Listing8OwnerSequence
