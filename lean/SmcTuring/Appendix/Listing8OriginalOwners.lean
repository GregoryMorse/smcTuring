module
public import SmcTuring.Appendix.Listing8OriginalPointer
public import SmcTuring.Appendix.Listing8OwnerSequence

public section
namespace SmcTuring.Appendix.Listing8OriginalOwners
open Native Listing8Prototypes
inductive Owner (mode : Mode) where
  | pointer (pc : Nat) (value : Word mode)
  | scalar (pc : Nat) (value : BitVec 32)
@[expose] def pc (mode : Mode) : Owner mode → Nat | .pointer pc _ => pc | .scalar pc _ => pc
@[expose] def span (mode : Mode) : Owner mode → Nat | .pointer _ _ => pointerSpan mode | .scalar _ _ => 10
@[expose] def Current (mode : Mode) (owner : Owner mode) (memory : ByteMemory.Memory) : Prop :=
  match owner with
  | .pointer pc value => ByteMemory.bytesAt memory pc (pointerBytes mode pc value).length=pointerBytes mode pc value
  | .scalar pc value => ByteMemory.bytesAt memory pc 10=DwordOwner.bytes mode pc value
@[expose] def Valid (mode : Mode) : Owner mode → Prop
  | .pointer pc value => pc+pointerSpan mode<2^(8*mode.wordBytes) ∧
      (value.toNat+mode.wordBytes ≤ pc ∨ pc+pointerSpan mode ≤ value.toNat)
  | .scalar pc _ => pc+10<2^(8*mode.wordBytes)
@[expose] def forms (mode : Mode) : Owner mode → List (StringDword.Form mode)
  | .pointer pc value => (Listing8CopiedPointer.forms mode pc pc value).map StringDword.Form.string
  | .scalar pc value => [StringDword.store mode (Relocation.memoryDisp mode (pc+10) (pc+6)) value]
@[expose] def advance (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode) :=
  match owner with
  | .pointer pc value => Listing8CopiedPointer.finish mode pc pc value state
  | .scalar pc value => StringDword.execute mode (StringDword.store mode (Relocation.memoryDisp mode (pc+10) (pc+6)) value) state
@[expose] def accumulator (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode) :=
  match owner with
  | .pointer _ value => Execution.load mode state.principal.memory value
  | .scalar _ _ => state.principal.accumulator
@[expose] def Contiguous (mode : Mode) : Nat → List (Owner mode) → Prop
  | _,[] => True
  | start,owner::owners => pc mode owner=start ∧ Contiguous mode (pc mode owner+span mode owner) owners
@[expose] def Intact (mode : Mode) (owners : List (Owner mode)) (memory : ByteMemory.Memory) := ∀ owner∈owners,Current mode owner memory
@[expose] def program (mode : Mode) (owners : List (Owner mode)) := owners.flatMap (forms mode)
@[expose] def finish (mode : Mode) (owners : List (Owner mode)) (state : StringExecution.State mode) := owners.foldl (fun state owner => advance mode owner state) state
@[expose] def total (mode : Mode) : List (Owner mode) → Nat | [] => 0 | owner::owners => span mode owner+total mode owners

theorem advance_effect (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode owner) (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner))
    (current : Current mode owner state.principal.memory) :
    advance mode owner state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (pc mode owner+span mode owner)
      accumulator:=accumulator mode owner state}} := by
  cases owner with
  | pointer pc value => exact Listing8OriginalPointer.effect mode pc value state entry valid.1 current
  | scalar pc value =>
    have targetFits : pc+6<2^(8*mode.wordBytes) := by change pc+10<_ at valid;omega
    have effect:=DwordArithmetic.located_effect mode (.store 0 value) pc (pc+6) state.principal rfl entry
      (fun _ => DwordOwner.reach pc) targetFits
    change DwordArithmetic.execute mode (.store (Relocation.memoryDisp mode (pc+10) (pc+6)) value) state.principal=
      {state.principal with pc:=Arithmetic.encodeNat mode (pc+10),memory:=DwordCode.put state.principal.memory (pc+6) value} at effect
    have valueBytes:=DwordOwner.current_immediate mode pc value state.principal.memory current
    have back : DwordCode.put state.principal.memory (pc+6) value=state.principal.memory := by
      exact ByteMemory.put_current state.principal.memory (pc+6) (LittleEndian.wordEncode 4 value) (by simpa only [LittleEndian.word_encode_length] using valueBytes)
    rw [advance,StringDword.store_execute,effect,back];rfl

theorem advance_trace (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode owner) (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner))
    (current : Current mode owner state.principal.memory) :
    StringDword.Trace mode state (forms mode owner) (advance mode owner state) := by
  cases owner with
  | pointer pc value => exact Listing8OriginalPointer.unified_trace mode pc value state entry valid.1 valid.2 current
  | scalar pc value =>
    have fits : pc<2^(8*mode.wordBytes) := by change pc+10<_ at valid;omega
    refine .step ?_ (.nil _)
    change state.principal.pc=Arithmetic.encodeNat mode pc at entry
    rw [entry,Arithmetic.encode_nat_toNat mode pc fits]
    exact StringDword.store_encoding mode _ _ _ _ current

/-- Entire original owner sequences execute from their initial packets;
each actual primitive restores whole memory before the next current fetch. -/
theorem trace (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    StringDword.Trace mode state (program mode owners) (finish mode owners state) := by
  induction owners generalizing start state with
  | nil => exact .nil _
  | cons owner owners ih =>
    have v:=valid owner (List.mem_cons_self ..)
    have c:=current owner (List.mem_cons_self ..)
    have loc : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have first:=advance_trace mode owner state v loc c
    have effect:=advance_effect mode owner state v loc c
    have next : (advance mode owner state).principal.pc=Arithmetic.encodeNat mode (pc mode owner+span mode owner) := by rw [effect]
    have remaining : Intact mode owners (advance mode owner state).principal.memory := by
      rw [effect];intro reader member;exact current reader (List.mem_cons_of_mem _ member)
    have rest:=ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next remaining
    simpa only [program,List.flatMap_cons,finish,List.foldl_cons] using StringDword.trace_append mode first rest

theorem result (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    (finish mode owners state).principal.pc=Arithmetic.encodeNat mode (start+total mode owners) ∧
    (finish mode owners state).principal.memory=state.principal.memory ∧
    (finish mode owners state).principal.stack=state.principal.stack ∧
    (finish mode owners state).principal.carry=state.principal.carry ∧
    (finish mode owners state).sourceIndex=state.sourceIndex ∧
    (finish mode owners state).destinationIndex=state.destinationIndex ∧
    (finish mode owners state).backwards=state.backwards := by
  induction owners generalizing start state with
  | nil => exact ⟨by simpa only [finish,List.foldl_nil,total,Nat.add_zero] using entry,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | cons owner owners ih =>
    have v:=valid owner (List.mem_cons_self ..)
    have c:=current owner (List.mem_cons_self ..)
    have loc : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have effect:=advance_effect mode owner state v loc c
    have next : (advance mode owner state).principal.pc=Arithmetic.encodeNat mode (pc mode owner+span mode owner) := by rw [effect]
    have remaining : Intact mode owners (advance mode owner state).principal.memory := by
      rw [effect];intro reader member;exact current reader (List.mem_cons_of_mem _ member)
    have rest:=ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next remaining
    simpa only [finish,List.foldl_cons,effect,total,chain.1,Nat.add_assoc] using rest
end SmcTuring.Appendix.Listing8OriginalOwners
