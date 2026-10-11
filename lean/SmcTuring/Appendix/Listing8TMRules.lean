module
public import SmcTuring.FrozenTM
public import SmcTuring.Appendix.Listing8GraphStep
public import Batteries.Data.Fin.Lemmas

public section
namespace SmcTuring.Appendix.Listing8TMRules
open Listing8SourceGraph

@[expose] def encode {alphabet : Nat} (symbol : Fin alphabet) : BitVec 32 := BitVec.ofNat 32 symbol.val
@[expose] def sentinel (alphabet : Nat) : BitVec 32 := BitVec.ofNat 32 alphabet
@[expose] def index {alphabet states : Nat} (state : Fin states) (slot : Fin (alphabet+1)) : Fin (states*(alphabet+1)) :=
  Fin.mkDivMod state slot
@[expose] def entry {alphabet states : Nat} (state : Fin states) : Fin (states*(alphabet+1)) := index state ⟨0,by omega⟩
@[expose] def symbolSlot {alphabet : Nat} (symbol : Fin alphabet) : Fin (alphabet+1) := ⟨symbol.val,by have := symbol.isLt;omega⟩
@[expose] def endSlot (alphabet : Nat) : Fin (alphabet+1) := ⟨alphabet,by omega⟩

/-- Missing entries and the explicit end rule use a reserved, unmatchable DWORD.
They preserve tape and head through the interpreter's mismatch branch. Every
state, including a state with no transitions, has an actual entry rule. -/
@[expose] def slotRule {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (slot : Fin (alphabet+1)) : Rule (states*(alphabet+1)) :=
  if valid : slot.val<alphabet then
    match machine.transition state ⟨slot.val,valid⟩ with
    | some (fresh,right,target) =>
      {symbol:=BitVec.ofNat 32 slot.val,fresh:=encode fresh,takeBack:=!right,
       scanNext:=true,destination:=some (entry target)}
    | none => {symbol:=sentinel alphabet,fresh:=sentinel alphabet,takeBack:=false,scanNext:=true,destination:=none}
  else {symbol:=sentinel alphabet,fresh:=sentinel alphabet,takeBack:=false,scanNext:=false,destination:=none}
@[expose] def rule {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (selected : Fin (states*(alphabet+1))) : Rule (states*(alphabet+1)) :=
  slotRule machine selected.divNat selected.modNat

theorem encode_toNat {alphabet : Nat} (capacity : alphabet<2^32) (symbol : Fin alphabet) :
    (encode symbol).toNat=symbol.val := by
  rw [encode,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_trans symbol.isLt capacity)]
theorem encode_injective {alphabet : Nat} (capacity : alphabet<2^32) (first second : Fin alphabet) :
    encode first=encode second ↔ first=second := by
  constructor
  · intro same
    apply Fin.ext
    have observed:=congrArg BitVec.toNat same
    simpa only [encode_toNat capacity] using observed
  · intro same;rw [same]
theorem sentinel_ne {alphabet : Nat} (capacity : alphabet<2^32) (symbol : Fin alphabet) :
    sentinel alphabet≠encode symbol := by
  intro same
  have observed:=congrArg BitVec.toNat same
  rw [sentinel,BitVec.toNat_ofNat,Nat.mod_eq_of_lt capacity,encode_toNat capacity] at observed
  have := symbol.isLt
  omega
theorem index_lookup {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (slot : Fin (alphabet+1)) :
    rule machine (index state slot)=slotRule machine state slot := by
  simp only [rule,index,Fin.divNat_mkDivMod,Fin.modNat_mkDivMod]
theorem index_value {alphabet states : Nat} (state : Fin states) (slot : Fin (alphabet+1)) :
    (index state slot).val=(alphabet+1)*state.val+slot.val := rfl
theorem entry_value {alphabet states : Nat} (state : Fin states) :
    (entry (alphabet:=alphabet) state).val=(alphabet+1)*state.val := by
  simp only [entry,index_value,Nat.add_zero]
theorem active {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (symbol fresh : Fin alphabet) (right : Bool) (target : Fin states)
    (selected : machine.transition state symbol=some (fresh,right,target)) :
    rule machine (index state (symbolSlot symbol))=
      {symbol:=encode symbol,fresh:=encode fresh,takeBack:=!right,scanNext:=true,destination:=some (entry target)} := by
  rw [index_lookup]
  simp only [slotRule,symbolSlot,symbol.isLt,dite_true,selected,encode]
theorem missing {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (symbol : Fin alphabet) (absent : machine.transition state symbol=none) :
    rule machine (index state (symbolSlot symbol))=
      {symbol:=sentinel alphabet,fresh:=sentinel alphabet,takeBack:=false,scanNext:=true,destination:=none} := by
  rw [index_lookup]
  simp only [slotRule,symbolSlot,symbol.isLt,dite_true,absent]
theorem terminal {alphabet states : Nat} (machine : TM.Machine alphabet states) (state : Fin states) :
    rule machine (index state (endSlot alphabet))=
      {symbol:=sentinel alphabet,fresh:=sentinel alphabet,takeBack:=false,scanNext:=false,destination:=none} := by
  rw [index_lookup]
  simp [slotRule,endSlot]
theorem scan_allowed {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (slot : Fin (alphabet+1)) (before : slot.val<alphabet) :
    (rule machine (index state slot)).scanNext=true := by
  rw [index_lookup]
  simp only [slotRule,before,dite_true]
  cases machine.transition state ⟨slot.val,before⟩ <;> rfl

theorem different_symbol {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (state : Fin states) (candidate input : Fin alphabet)
    (different : candidate≠input) :
    (rule machine (index state (symbolSlot candidate))).symbol≠encode input := by
  cases h : machine.transition state candidate with
  | none =>
    rw [missing machine state candidate h]
    exact sentinel_ne capacity input
  | some result =>
    rcases result with ⟨fresh,right,target⟩
    rw [active machine state candidate fresh right target h]
    exact fun same => different ((encode_injective capacity candidate input).mp same)

theorem missing_symbol {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (state : Fin states) (candidate input : Fin alphabet)
    (absent : machine.transition state candidate=none) :
    (rule machine (index state (symbolSlot candidate))).symbol≠encode input := by
  rw [missing machine state candidate absent]
  exact sentinel_ne capacity input
theorem terminal_symbol {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (capacity : alphabet<2^32) (state : Fin states) (input : Fin alphabet) :
    (rule machine (index state (endSlot alphabet))).symbol≠encode input := by
  rw [terminal]
  exact sentinel_ne capacity input

theorem frozen_rule {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (selected : Fin (states*(alphabet+1))) :
    rule (TM.thaw (TM.freeze machine)) selected=rule machine selected := by rw [TM.thaw_freeze]

theorem empty_frozen_row {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (state : Fin states) (empty : (machine.table[state.val]?).getD []=[]) (symbol : Fin alphabet) :
    (TM.thaw machine).transition state symbol=none := by
  simp only [TM.thaw,empty,List.getElem?_nil,Option.getD_none]

end SmcTuring.Appendix.Listing8TMRules
