module
public import SmcTuring.SMC.ComputableTable
public import SmcTuring.SMC.ConcreteFiniteExecution

public section

namespace SmcTuring.SMC.Effective

open Dolan Dolan.Encoding

variable {alphabet states : Nat}

abbrev SymbolInput (alphabet states : Nat) := Prod (TM.Machine alphabet states) (Prod (List (Fin alphabet)) Nat)

/-- The initialized two-sided tape, indexed by the canonical natural address
of a signed tape position. Odd indices denote the blank negative half. -/
@[expose] def initialSymbol (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (index : Nat) : Fin alphabet :=
  if index % 2 = 1 then machine.blank else (input[index / 2]?).getD machine.blank

theorem initial_symbol_primrec : Primrec (fun input : SymbolInput alphabet states => initialSymbol input.1 input.2.1 input.2.2) := by
  have machine : Primrec (fun input : SymbolInput alphabet states => input.1) := Primrec.fst
  have symbols : Primrec (fun input : SymbolInput alphabet states => input.2.1) := Primrec.fst.comp Primrec.snd
  have index : Primrec (fun input : SymbolInput alphabet states => input.2.2) := Primrec.snd.comp Primrec.snd
  have blank := machine_blank_primrec.comp machine
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp index (Primrec.const 2)) (Primrec.const 1)) blank
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp symbols (Primrec.nat_div.comp index (Primrec.const 2))) blank)

theorem initial_symbol_correct (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (index : Nat) :
    initialSymbol machine input index = (TM.initialConfiguration machine input).tape (unzigzag index) := by
  have bound := Nat.mod_lt index (by decide : 0 < 2)
  by_cases even : index % 2 = 0
  · have positive : ¬ ((index / 2 : Nat) : Int) < 0 := by omega
    simp only [initialSymbol, TM.initialConfiguration, unzigzag, even, ite_true, Int.toNat_natCast, Int.ofNat_eq_natCast]
    simp only [Nat.zero_ne_one, positive, ite_false]
  · have odd : index % 2 = 1 := by omega
    simp [initialSymbol, TM.initialConfiguration, unzigzag, odd]

/-- Moving outward on either half of the initialized tape increases its
canonical natural position code by two. -/
theorem zigzag_outward (position : Int) :
    zigzag (if position < 0 then position - 1 else position + 1) = zigzag position + 2 := by
  cases position with
  | ofNat n =>
    have moved : Int.ofNat n + 1 = Int.ofNat (n + 1) := by simp only [Int.ofNat_eq_natCast]; omega
    have positive : ¬ Int.ofNat n < 0 := by simp only [Int.ofNat_eq_natCast]; omega
    simp only [positive, ite_false, moved, zigzag]
    omega
  | negSucc n =>
    have moved : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    simp [moved, zigzag]
    omega

abbrev HeapInput (alphabet states : Nat) := Prod (TM.Machine alphabet states) (Prod (List (Fin alphabet)) (Prod Nat Bool))

@[expose] def initializedTape (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (p : Prod Nat Bool) : Mov.Word :=
  if p.1 < Table.tableLimit alphabet states then .offset false else
  if p.2 then .address (p.1 + 2) else
    .address ((initialSymbol machine input (p.1 - Table.tableLimit alphabet states)).val + 1)

theorem initialized_tape_primrec : Primrec (fun input : HeapInput alphabet states => initializedTape input.1 input.2.1 input.2.2) := by
  have machine : Primrec (fun input : HeapInput alphabet states => input.1) := Primrec.fst
  have symbols : Primrec (fun input : HeapInput alphabet states => input.2.1) := Primrec.fst.comp Primrec.snd
  have cell : Primrec (fun input : HeapInput alphabet states => input.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have choice : Primrec (fun input : HeapInput alphabet states => input.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have symbol := initial_symbol_primrec.comp (Primrec.pair machine (Primrec.pair symbols (Primrec.nat_sub.comp cell (Primrec.const (Table.tableLimit alphabet states)))))
  exact (Primrec.ite (Primrec.nat_lt.comp cell (Primrec.const (Table.tableLimit alphabet states)))
    (Primrec.const (Mov.Word.offset false))
    (Primrec.cond choice (word_address_primrec.comp (Primrec.nat_add.comp cell (Primrec.const 2)))
      (word_address_primrec.comp (Primrec.succ.comp (Primrec.fin_val.comp symbol))))).of_eq fun input => by
    cases h : input.2.2.2 <;> simp [initializedTape, h]

theorem initialized_tape_correct (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (p : Prod Nat Bool) :
    initializedTape machine input p = Encoding.encodedMemory (5 * (alphabet * states)) (TM.initialConfiguration machine input) p := by
  have base : alphabet + 5 * (alphabet * states) + 1 = Table.tableLimit alphabet states := by
    unfold Table.tableLimit
    omega
  by_cases low : p.1 < Table.tableLimit alphabet states
  · simp [initializedTape, Encoding.encodedMemory, base, low]
  · cases p with
      | mk cell choice =>
        cases choice
        · simp [initializedTape, Encoding.encodedMemory, base, low, Encoding.standardLayout, initial_symbol_correct]
        · simp only [initializedTape, low, ite_false, ite_true,
            Encoding.encodedMemory, base, Encoding.standardLayout, TM.initialConfiguration]
          rw [zigzag_outward, zigzag_unzigzag]
          congr 1
          omega

@[expose] def initializedHeap (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (p : Prod Nat Bool) : Mov.Word :=
  if p.1 < Table.tableLimit alphabet states then tableFromCache machine p else initializedTape machine input p

theorem initialized_heap_primrec : Primrec (fun input : HeapInput alphabet states => initializedHeap input.1 input.2.1 input.2.2) := by
  have cell : Primrec (fun input : HeapInput alphabet states => input.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.nat_lt.comp cell (Primrec.const (Table.tableLimit alphabet states)))
    (table_from_cache_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)) initialized_tape_primrec

theorem initialized_heap_correct (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (p : Prod Nat Bool) :
    initializedHeap machine input p = Table.initialMemory machine (TM.initialConfiguration machine input) p := by
  by_cases low : p.1 < Table.tableLimit alphabet states
  · simp [initializedHeap, Table.initialMemory, low, table_from_cache_correct machine p low]
  · simp [initializedHeap, Table.initialMemory, low, initialized_tape_correct]

/-- Natural values of words in the actual unit-stride register/heap layout. -/
@[expose] def wordNatural : Mov.Word -> Nat
  | .address cell => 13 + 2 * cell
  | .offset choice => if choice then 1 else 0

theorem word_natural_primrec : Primrec wordNatural := by
  have address : Primrec (fun cell : Nat => 13 + 2 * cell) := Primrec.nat_add.comp (Primrec.const 13) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
  have offset : Primrec (fun choice : Bool => if choice then (1 : Nat) else 0) :=
    (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq fun choice => by cases choice <;> rfl
  exact (Primrec.sumCasesOn word_codec_primrec (address.comp Primrec.snd).to₂ (offset.comp Primrec.snd).to₂).of_eq
    fun word => by cases word <;> rfl

theorem encode_word_natural (word : Mov.Word) : encodeWord Concrete.dataLayout.data word = Int.ofNat (wordNatural word) := by
  cases word with
  | address cell => simp [encodeWord, heapField, fieldAddress, Concrete.dataLayout, wordNatural]
  | offset choice => cases choice <;> rfl

theorem int_of_nat_primrec : Primrec Int.ofNat :=
  (unzigzag_primrec.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq
    fun n => unzigzag_zigzag (Int.ofNat n)

abbrev RegisterInput (alphabet states : Nat) := Prod (TM.Machine alphabet states) (List (Fin alphabet))

theorem initialized_register_fixed_primrec (register : Mov.Register) :
    Primrec (fun input : RegisterInput alphabet states =>
      (Mov.initialKernelState input.1 (TM.initialConfiguration input.1 input.2)).registers register) := by
  cases register <;> simp only [Mov.initialKernelState, TM.initialConfiguration]
  all_goals first
    | exact Primrec.const _
    | exact word_address_primrec.comp (table_head_primrec.comp Primrec.fst (machine_start_primrec.comp Primrec.fst))

@[expose] def initialRegisterCache (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) : List Mov.Word :=
  List.ofFn (fun index : Fin 13 => (Mov.initialKernelState machine (TM.initialConfiguration machine input)).registers (Four.registerAt index))

theorem initial_register_cache_primrec : Primrec₂ (initialRegisterCache (alphabet := alphabet) (states := states)) :=
  Primrec.list_ofFn fun index => initialized_register_fixed_primrec (Four.registerAt index)

abbrev DataInput (alphabet states : Nat) := Prod (TM.Machine alphabet states) (Prod (List (Fin alphabet)) Nat)

@[expose] def initializedDataWord (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (field : Nat) : Mov.Word :=
  if field < 13 then ((initialRegisterCache machine input)[field]?).getD (.offset false)
  else initializedHeap machine input ((field - 13) / 2, decide ((field - 13) % 2 = 1))

theorem initialized_data_word_primrec : Primrec (fun input : DataInput alphabet states => initializedDataWord input.1 input.2.1 input.2.2) := by
  have machine : Primrec (fun input : DataInput alphabet states => input.1) := Primrec.fst
  have symbols : Primrec (fun input : DataInput alphabet states => input.2.1) := Primrec.fst.comp Primrec.snd
  have field : Primrec (fun input : DataInput alphabet states => input.2.2) := Primrec.snd.comp Primrec.snd
  have relative := Primrec.nat_sub.comp field (Primrec.const 13)
  have choice := (Primrec.eq.comp (Primrec.nat_mod.comp relative (Primrec.const 2)) (Primrec.const 1)).decide
  exact Primrec.ite (Primrec.nat_lt.comp field (Primrec.const 13))
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (initial_register_cache_primrec.comp machine symbols) field) (Primrec.const (Mov.Word.offset false)))
    (initialized_heap_primrec.comp (Primrec.pair machine (Primrec.pair symbols (Primrec.pair (Primrec.nat_div.comp relative (Primrec.const 2)) choice))))

theorem initialized_data_word_correct (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (field : Nat) :
    initializedDataWord machine input field =
      if h : field < 13 then (Mov.initialKernelState machine (TM.initialConfiguration machine input)).registers (Four.registerAt ⟨field, h⟩)
      else (Mov.initialKernelState machine (TM.initialConfiguration machine input)).memory ((field - 13) / 2, decide ((field - 13) % 2 = 1)) := by
  by_cases low : field < 13
  · simp only [initializedDataWord, low, ite_true, dite_true, initialRegisterCache, List.getElem?_ofFn, Option.getD_some]
  · simp [initializedDataWord, low, initialized_heap_correct, Mov.initialKernelState]

theorem initialized_data_memory_correct (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (field : Nat) :
    encodeWord Concrete.dataLayout.data (initializedDataWord machine input field) =
      Virtual.dataMemory Concrete.dataLayout (Mov.initialKernelState machine (TM.initialConfiguration machine input)) (Int.ofNat field) := by
  rw [initialized_data_word_correct]
  by_cases low : field < 13 <;> simp [Virtual.dataMemory, Virtual.fieldIndex, Concrete.dataLayout, low]

@[expose] def initializedDataCode (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (field : Nat) : Nat :=
  2 * wordNatural (initializedDataWord machine input field)

theorem initialized_data_code_primrec : Primrec (fun input : DataInput alphabet states => initializedDataCode input.1 input.2.1 input.2.2) :=
  Primrec.nat_mul.comp (Primrec.const 2) (word_natural_primrec.comp initialized_data_word_primrec)

theorem initialized_data_code_correct (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (field : Nat) :
    initializedDataCode machine input field = zigzag
      (Virtual.dataMemory Concrete.dataLayout (Mov.initialKernelState machine (TM.initialConfiguration machine input)) (Int.ofNat field)) := by
  rw [←initialized_data_memory_correct, encode_word_natural]
  rfl

/-- All potentially negative metadata words occupy a fixed finite cache.
The thirteen low slots are computed directly, for every natural index. -/
@[expose] def metadataCode (index : Nat) : Nat :=
  if index < 13 then 2 * index else
    ((List.ofFn (fun slot : Fin 38 => zigzag (Concrete.metadataValue slot.val)))[index]?).getD 0

theorem metadata_code_primrec : Primrec metadataCode :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 13))
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (Primrec.const (List.ofFn (fun slot : Fin 38 => zigzag (Concrete.metadataValue slot.val)))) Primrec.id)
      (Primrec.const 0))

theorem metadata_code_correct (index : Nat) : metadataCode index = zigzag (Concrete.metadataValue index) := by
  by_cases low : index < 13
  · simp only [metadataCode, Concrete.metadataValue, low, ite_true, zigzag]
  · by_cases inside : index < 38
    · simp only [metadataCode, low, ite_false, List.getElem?_ofFn, inside, dite_true, Option.getD_some]
    · have zero : Concrete.metadataValue index = 0 := by
        simp only [Concrete.metadataValue, low, ite_false]
        split <;> first | rfl | omega
      simp only [metadataCode, low, ite_false, List.getElem?_ofFn, inside, dite_false, Option.getD_none, zero, zigzag]

abbrev InitialWordInput (alphabet states : Nat) := Prod (TM.FrozenMachine alphabet states) (Prod (List (Fin alphabet)) Nat)

/-- A closed initial-word generator over the finite frozen machine/input and a
canonical address. No function-valued memory input occurs in this algorithm. -/
@[expose] def initialWordCode (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (field : Nat) : Nat :=
  if field % 2 = 0 then initializedDataCode (TM.thaw machine) input (field / 2) else metadataCode (field / 2)

theorem initial_word_code_primrec : Primrec (fun input : InitialWordInput alphabet states => initialWordCode input.1 input.2.1 input.2.2) := by
  have machine : Primrec (fun input : InitialWordInput alphabet states => TM.thaw input.1) := thaw_primrec.comp Primrec.fst
  have symbols : Primrec (fun input : InitialWordInput alphabet states => input.2.1) := Primrec.fst.comp Primrec.snd
  have field : Primrec (fun input : InitialWordInput alphabet states => input.2.2) := Primrec.snd.comp Primrec.snd
  have magnitude := Primrec.nat_div.comp field (Primrec.const 2)
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp field (Primrec.const 2)) (Primrec.const 0))
    (initialized_data_code_primrec.comp (Primrec.pair machine (Primrec.pair symbols magnitude)))
    (metadata_code_primrec.comp magnitude)

theorem initial_word_code_correct (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (field : Nat) :
    initialWordCode machine input field = zigzag (Concrete.initialWords machine input (unzigzag field)) := by
  by_cases even : field % 2 = 0
  · have positive : 0 ≤ ((field / 2 : Nat) : Int) := by omega
    simp only [initialWordCode, even, ite_true, initialized_data_code_correct, Concrete.initialWords,
      Concrete.initialTMState, Concrete.initialState, Concrete.initialMemory, unzigzag, Int.ofNat_eq_natCast, positive]
  · simp only [initialWordCode, even, ite_false, metadata_code_correct]
    simp [Concrete.initialWords, Concrete.initialTMState, Concrete.initialState, Concrete.initialMemory, unzigzag, even]
    rfl

end SmcTuring.SMC.Effective
