module
public import SmcTuring.SMC.ComputableFixedHeaders
public import SmcTuring.FrozenTM
public import SmcTuring.Dolan.TableLayout

public section

namespace SmcTuring.SMC.Effective

abbrev TransitionData (alphabet states : Nat) := Option (Prod (Fin alphabet) (Prod Bool (Fin states)))
abbrev MachineData (alphabet states : Nat) :=
  Prod (Fin alphabet) (Prod (Fin states) (Fin states -> Fin alphabet -> TransitionData alphabet states))
abbrev FrozenData (alphabet states : Nat) :=
  Prod (Fin alphabet) (Prod (Fin states) (List (List (TransitionData alphabet states))))
abbrev EntryData (alphabet states : Nat) := Prod (Fin alphabet) (Prod (Fin alphabet) (Prod Bool (Fin states)))

/-- Finite transition functions use Mathlib's vector encoding of finite-domain
functions. An unbounded function cannot inhabit this machine descriptor. -/
@[expose] def machineEquiv (alphabet states : Nat) : Equiv (TM.Machine alphabet states) (MachineData alphabet states) where
  toFun machine := (machine.blank, machine.start, machine.transition)
  invFun data := { blank := data.1, start := data.2.1, transition := data.2.2 }
  left_inv machine := by cases machine; rfl
  right_inv data := by rcases data with ⟨blank, start, transition⟩; rfl

@[expose] def frozenEquiv (alphabet states : Nat) : Equiv (TM.FrozenMachine alphabet states) (FrozenData alphabet states) where
  toFun machine := (machine.blank, machine.start, machine.table)
  invFun data := { blank := data.1, start := data.2.1, table := data.2.2 }
  left_inv machine := by cases machine; rfl
  right_inv data := by rcases data with ⟨blank, start, table⟩; rfl

@[expose] def entryEquiv (alphabet states : Nat) : Equiv (Dolan.Table.Entry alphabet states) (EntryData alphabet states) where
  toFun entry := (entry.trigger, entry.symbol, entry.direction, entry.destination)
  invFun data := { trigger := data.1, symbol := data.2.1, direction := data.2.2.1, destination := data.2.2.2 }
  left_inv entry := by cases entry; rfl
  right_inv data := by rcases data with ⟨trigger, symbol, direction, destination⟩; rfl

@[expose] def wordEquiv : Equiv Dolan.Mov.Word (Sum Nat Bool) where
  toFun word := match word with
    | .address cell => Sum.inl cell
    | .offset choice => Sum.inr choice
  invFun data := match data with
    | .inl cell => .address cell
    | .inr choice => .offset choice
  left_inv word := by cases word <;> rfl
  right_inv data := by cases data <;> rfl

instance machinePrimcodable (alphabet states : Nat) : Primcodable (TM.Machine alphabet states) :=
  Primcodable.ofEquiv (MachineData alphabet states) (machineEquiv alphabet states)
instance frozenPrimcodable (alphabet states : Nat) : Primcodable (TM.FrozenMachine alphabet states) :=
  Primcodable.ofEquiv (FrozenData alphabet states) (frozenEquiv alphabet states)
instance entryPrimcodable (alphabet states : Nat) : Primcodable (Dolan.Table.Entry alphabet states) :=
  Primcodable.ofEquiv (EntryData alphabet states) (entryEquiv alphabet states)
instance wordPrimcodable : Primcodable Dolan.Mov.Word := Primcodable.ofEquiv (Sum Nat Bool) wordEquiv

variable {alphabet states : Nat}

theorem machine_codec_primrec : Primrec (machineEquiv alphabet states) := Primrec.of_equiv

theorem machine_constructor_primrec : Primrec (machineEquiv alphabet states).symm := Primrec.of_equiv_symm

theorem frozen_codec_primrec : Primrec (frozenEquiv alphabet states) := Primrec.of_equiv

theorem frozen_constructor_primrec : Primrec (frozenEquiv alphabet states).symm := Primrec.of_equiv_symm

theorem entry_codec_primrec : Primrec (entryEquiv alphabet states) := Primrec.of_equiv

theorem entry_constructor_primrec : Primrec (entryEquiv alphabet states).symm := Primrec.of_equiv_symm

theorem word_codec_primrec : Primrec wordEquiv := Primrec.of_equiv

theorem word_constructor_primrec : Primrec wordEquiv.symm := Primrec.of_equiv_symm

theorem word_address_primrec : Primrec Dolan.Mov.Word.address := by
  exact (word_constructor_primrec.comp Primrec.sumInl).of_eq fun cell => by rfl

theorem word_offset_primrec : Primrec Dolan.Mov.Word.offset := by
  exact (word_constructor_primrec.comp Primrec.sumInr).of_eq fun choice => by rfl

theorem machine_blank_primrec : Primrec (fun machine : TM.Machine alphabet states => machine.blank) :=
  Primrec.fst.comp machine_codec_primrec

theorem machine_start_primrec : Primrec (fun machine : TM.Machine alphabet states => machine.start) :=
  Primrec.fst.comp (Primrec.snd.comp machine_codec_primrec)

theorem machine_transition_primrec : Primrec (fun machine : TM.Machine alphabet states => machine.transition) :=
  Primrec.snd.comp (Primrec.snd.comp machine_codec_primrec)

theorem frozen_blank_primrec : Primrec (fun machine : TM.FrozenMachine alphabet states => machine.blank) :=
  Primrec.fst.comp frozen_codec_primrec

theorem frozen_start_primrec : Primrec (fun machine : TM.FrozenMachine alphabet states => machine.start) :=
  Primrec.fst.comp (Primrec.snd.comp frozen_codec_primrec)

theorem frozen_table_primrec : Primrec (fun machine : TM.FrozenMachine alphabet states => machine.table) :=
  Primrec.snd.comp (Primrec.snd.comp frozen_codec_primrec)

/-- The actual frozen-table lookup is certified, including short/missing rows. -/
theorem frozen_transition_primrec : Primrec (fun input : Prod (Prod (TM.FrozenMachine alphabet states) (Fin states)) (Fin alphabet) =>
    (TM.thaw input.1.1).transition input.1.2 input.2) := by
  have table : Primrec (fun input : Prod (Prod (TM.FrozenMachine alphabet states) (Fin states)) (Fin alphabet) => input.1.1.table) :=
    frozen_table_primrec.comp (Primrec.fst.comp Primrec.fst)
  have stateIndex : Primrec (fun input : Prod (Prod (TM.FrozenMachine alphabet states) (Fin states)) (Fin alphabet) => input.1.2.val) := Primrec.fin_val.comp (Primrec.snd.comp Primrec.fst)
  have symbolIndex : Primrec (fun input : Prod (Prod (TM.FrozenMachine alphabet states) (Fin states)) (Fin alphabet) => input.2.val) := Primrec.fin_val.comp Primrec.snd
  have row := Primrec.option_getD.comp (Primrec.list_getElem?.comp table stateIndex) (Primrec.const [])
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp row symbolIndex) (Primrec.const none)

theorem thaw_primrec : Primrec (TM.thaw (alphabet := alphabet) (states := states)) := by
  have transition : Primrec (fun machine : TM.FrozenMachine alphabet states => (TM.thaw machine).transition) :=
    Primrec.fin_curry.mpr (Primrec.fin_curry.mpr frozen_transition_primrec)
  exact (machine_constructor_primrec.comp (Primrec.pair frozen_blank_primrec (Primrec.pair frozen_start_primrec transition))).of_eq
    fun machine => by rfl

theorem transition_primrec : Primrec (fun input : Prod (Prod (TM.Machine alphabet states) (Fin states)) (Fin alphabet) =>
    input.1.1.transition input.1.2 input.2) :=
  Primrec.fin_app.comp
    (Primrec.fin_app.comp (machine_transition_primrec.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)) Primrec.snd

/-- Filtering a state's transition row is a computation on finite encoded
machine data. Undefined transitions are omitted in the published order. -/
theorem entries_primrec : Primrec₂ (fun machine : TM.Machine alphabet states => Dolan.Table.entries machine) := by
  have transition := transition_primrec (alphabet := alphabet) (states := states)
  have entry : Primrec₂ (fun input : Prod (TM.Machine alphabet states) (Fin states) =>
      fun trigger : Fin alphabet =>
        (input.1.transition input.2 trigger).map (fun result =>
          ({ trigger := trigger, symbol := result.1, direction := result.2.1, destination := result.2.2 } : Dolan.Table.Entry alphabet states))) :=
    Primrec.option_map transition
      (entry_constructor_primrec.comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst)
          (Primrec.pair (Primrec.fst.comp Primrec.snd)
            (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))).to₂
  exact Primrec.listFilterMap (Primrec.const (List.ofFn (fun symbol : Fin alphabet => symbol))) entry

end SmcTuring.SMC.Effective
