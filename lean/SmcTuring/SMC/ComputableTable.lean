module
public import SmcTuring.SMC.ComputableFiniteTypes

public section

namespace SmcTuring.SMC.Effective

open Dolan

variable {alphabet states : Nat}

/-- The actual node-address arithmetic, uniformly in the finite state and index. -/
theorem table_node_primrec : Primrec₂ (Table.node (states := states) alphabet) := by
  exact Primrec.nat_add.comp (Primrec.const (alphabet + 1))
    (Primrec.nat_mul.comp (Primrec.const 5)
      (Primrec.nat_add.comp Primrec.snd
        (Primrec.nat_mul.comp (Primrec.const alphabet) (Primrec.fin_val.comp Primrec.fst))))

abbrev CursorInput (alphabet states : Nat) := Prod (TM.Machine alphabet states) (Prod (Fin states) Nat)

theorem table_cursor_primrec : Primrec (fun input : CursorInput alphabet states =>
    Table.cursor input.1 input.2.1 input.2.2) := by
  have machine : Primrec (fun input : CursorInput alphabet states => input.1) := Primrec.fst
  have state : Primrec (fun input : CursorInput alphabet states => input.2.1) := Primrec.fst.comp Primrec.snd
  have index : Primrec (fun input : CursorInput alphabet states => input.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite
    (Primrec.nat_lt.comp index (Primrec.list_length.comp (entries_primrec.comp machine state)))
    (table_node_primrec.comp state index) (Primrec.const 0)

theorem table_head_primrec : Primrec₂ (Table.head (alphabet := alphabet) (states := states)) := by
  exact table_cursor_primrec.comp (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd (Primrec.const 0)))

abbrev RecordInput (alphabet states : Nat) :=
  Prod (TM.Machine alphabet states) (Prod (Fin states) (Prod Nat (Prod (Table.Entry alphabet states) (Prod Nat Bool))))

/-- All nine used linked-record fields and the unused/default field have finite
primitive-recursive generators. -/
theorem table_record_primrec : Primrec (fun input : RecordInput alphabet states =>
    Table.recordWord input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1 input.2.2.2.2.2) := by
  have machine : Primrec (fun input : RecordInput alphabet states => input.1) := Primrec.fst
  have state : Primrec (fun input : RecordInput alphabet states => input.2.1) := Primrec.fst.comp Primrec.snd
  have index : Primrec (fun input : RecordInput alphabet states => input.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have entry : Primrec (fun input : RecordInput alphabet states => input.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have component : Primrec (fun input : RecordInput alphabet states => input.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have choice : Primrec (fun input : RecordInput alphabet states => input.2.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have coded := entry_codec_primrec.comp entry
  have trigger := Primrec.fin_val.comp (Primrec.fst.comp coded)
  have symbol := Primrec.fin_val.comp (Primrec.fst.comp (Primrec.snd.comp coded))
  have direction := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp coded))
  have destination := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp coded))
  have node := (table_node_primrec (alphabet := alphabet)).comp state index
  have next := table_cursor_primrec.comp (Primrec.pair machine (Primrec.pair state (Primrec.succ.comp index)))
  have target := table_head_primrec.comp machine destination
  have slot0 := Primrec.cond choice (word_address_primrec.comp next) (word_address_primrec.comp (Primrec.succ.comp node))
  have slot1 := Primrec.cond choice (word_address_primrec.comp (Primrec.nat_add.comp node (Primrec.const 2))) (word_address_primrec.comp (Primrec.succ.comp trigger))
  have slot2 := Primrec.cond choice (word_address_primrec.comp (Primrec.nat_add.comp node (Primrec.const 3))) (word_address_primrec.comp (Primrec.succ.comp symbol))
  have slot3 := Primrec.cond choice (word_address_primrec.comp (Primrec.nat_add.comp node (Primrec.const 4))) (word_offset_primrec.comp direction)
  have slot4 := Primrec.cond choice (Primrec.const (Mov.Word.offset false)) (word_address_primrec.comp target)
  exact (Primrec.ite (Primrec.eq.comp component (Primrec.const 0)) slot0
    (Primrec.ite (Primrec.eq.comp component (Primrec.const 1)) slot1
      (Primrec.ite (Primrec.eq.comp component (Primrec.const 2)) slot2
        (Primrec.ite (Primrec.eq.comp component (Primrec.const 3)) slot3
          (Primrec.ite (Primrec.eq.comp component (Primrec.const 4)) slot4
            (Primrec.const (Mov.Word.offset false))))))).of_eq fun input => by
    rcases h : input.2.2.2.2.1 with _ | _ | _ | _ | _ | n <;>
      cases input.2.2.2.2.2 <;> simp [Table.recordWord, Bool.cond_eq_ite, entryEquiv]

/-- At a fixed cell, the finite row and candidate indices are constants. This
certificate covers the published table decoder, including missing entries. -/
theorem table_memory_fixed_primrec (cell : Nat) (choice : Bool) :
    Primrec (fun machine : TM.Machine alphabet states => Table.tableMemory machine (cell, choice)) := by
  unfold Table.tableMemory
  split
  · exact Primrec.const _
  · dsimp only
    split
    · rename_i valid
      let state : Fin states := ⟨((cell - (alphabet + 1)) / 5) / alphabet, valid⟩
      have entry : Primrec (fun machine : TM.Machine alphabet states => (Table.entries machine state)[((cell - (alphabet + 1)) / 5) % alphabet]?) := Primrec.list_getElem?.comp (entries_primrec.comp Primrec.id (Primrec.const state))
        (Primrec.const (((cell - (alphabet + 1)) / 5) % alphabet))
      exact (Primrec.option_casesOn entry (Primrec.const (Mov.Word.offset false))
        (table_record_primrec.comp (Primrec.pair Primrec.fst
          (Primrec.pair (Primrec.const state)
            (Primrec.pair (Primrec.const (((cell - (alphabet + 1)) / 5) % alphabet))
              (Primrec.pair Primrec.snd
                (Primrec.pair (Primrec.const ((cell - (alphabet + 1)) % 5)) (Primrec.const choice))))))).to₂).of_eq
        fun machine => by cases (Table.entries machine state)[((cell - (alphabet + 1)) / 5) % alphabet]? <;> rfl
    · exact Primrec.const _

/-- A finite cache of precisely the actual table words. Its size depends only
on the finite alphabet/state sizes, never on a simulated run. -/
@[expose] def tableCache (machine : TM.Machine alphabet states) : List (Prod Mov.Word Mov.Word) :=
  List.ofFn (fun index : Fin (Table.tableLimit alphabet states) =>
    (Table.tableMemory machine (index.val, false), Table.tableMemory machine (index.val, true)))

theorem table_cache_primrec : Primrec (tableCache (alphabet := alphabet) (states := states)) :=
  Primrec.list_ofFn fun index => Primrec.pair (table_memory_fixed_primrec index.val false) (table_memory_fixed_primrec index.val true)

@[expose] def tableFromCache (machine : TM.Machine alphabet states) (p : Prod Nat Bool) : Mov.Word :=
  let words := ((tableCache machine)[p.1]?).getD (.offset false, .offset false)
  if p.2 then words.2 else words.1

theorem table_from_cache_primrec : Primrec₂ (tableFromCache (alphabet := alphabet) (states := states)) := by
  have words : Primrec (fun input : Prod (TM.Machine alphabet states) (Prod Nat Bool) => ((tableCache input.1)[input.2.1]?).getD (Mov.Word.offset false, Mov.Word.offset false)) := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (table_cache_primrec.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.const (Mov.Word.offset false, Mov.Word.offset false))
  exact (Primrec.cond (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp words) (Primrec.fst.comp words)).of_eq fun input => by cases h : input.2.2 <;> simp [tableFromCache, h]

theorem table_from_cache_correct (machine : TM.Machine alphabet states) (p : Prod Nat Bool)
    (inside : p.1 < Table.tableLimit alphabet states) :
    tableFromCache machine p = Table.tableMemory machine p := by
  simp only [tableFromCache, tableCache, List.getElem?_ofFn, inside, dite_true, Option.getD_some]
  cases p with
  | mk cell choice => cases choice <;> rfl

end SmcTuring.SMC.Effective
