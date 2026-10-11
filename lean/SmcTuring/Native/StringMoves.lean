module
public import SmcTuring.Native.StringExecution

public section
namespace SmcTuring.Native.StringMoves
open StringExecution

@[expose] def view (mode : Mode) (state : State mode) : StringCopy.State :=
  ⟨state.sourceIndex.toNat,state.destinationIndex.toNat,state.principal.memory⟩
@[expose] def forms (mode : Mode) (widths : List Nat) : List (StringForm.Form mode) :=
  widths.map StringForm.Form.move
@[expose] def code (widths : List Nat) : List LittleEndian.Byte := (widths.map StringPlan.opcode).flatten
@[expose] def span (widths : List Nat) : Nat := (code widths).length

theorem code_cons (width : Nat) (rest : List Nat) : code (width::rest) = StringPlan.opcode width ++ code rest := rfl

theorem span_cons (width : Nat) (rest : List Nat) : span (width::rest) = (StringPlan.opcode width).length + span rest := by
  simp only [span,code_cons,List.length_append]

theorem index_advance (mode : Mode) (index : Word mode) (width : Nat)
    (fits : index.toNat+width < 2^(8*mode.wordBytes)) :
    (index+Arithmetic.encodeNat mode width).toNat = index.toNat+width := by
  have small : width < 2^(8*mode.wordBytes) := by omega
  change (index+BitVec.ofNat (8*mode.wordBytes) width).toNat = _
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt fits]

theorem move_view (mode : Mode) (width : Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+width < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+width < 2^(8*mode.wordBytes)) :
    view mode (execute mode (.move width) state) = StringCopy.execute width (view mode state) := by
  rw [move_effect mode width state forward]
  simp only [view,StringCopy.execute,index_advance mode _ width sourceFits,index_advance mode _ width destinationFits]

theorem run_view (mode : Mode) (widths : List Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes)) :
    view mode (run mode (forms mode widths) state) = StringCopy.run widths (view mode state) := by
  induction widths generalizing state with
  | nil => rfl
  | cons width rest ih =>
    have sourceHead : state.sourceIndex.toNat+width < 2^(8*mode.wordBytes) := by simp only [List.sum_cons] at sourceFits; omega
    have destinationHead : state.destinationIndex.toNat+width < 2^(8*mode.wordBytes) := by simp only [List.sum_cons] at destinationFits; omega
    have sourceNext : (execute mode (.move width) state).sourceIndex.toNat = state.sourceIndex.toNat+width := by
      rw [move_effect mode width state forward]
      exact index_advance mode _ _ sourceHead
    have destinationNext : (execute mode (.move width) state).destinationIndex.toNat = state.destinationIndex.toNat+width := by
      rw [move_effect mode width state forward]
      exact index_advance mode _ _ destinationHead
    have sourceTail : (execute mode (.move width) state).sourceIndex.toNat+rest.sum < 2^(8*mode.wordBytes) := by
      rw [sourceNext]; simpa only [List.sum_cons,Nat.add_assoc] using sourceFits
    have destinationTail : (execute mode (.move width) state).destinationIndex.toNat+rest.sum < 2^(8*mode.wordBytes) := by
      rw [destinationNext]; simpa only [List.sum_cons,Nat.add_assoc] using destinationFits
    change view mode (run mode (forms mode rest) (execute mode (.move width) state)) = _
    rw [ih _ ((direction_preserved mode _ state).trans forward) sourceTail destinationTail,
      move_view mode width state forward sourceHead destinationHead]
    rfl

theorem run_pc (mode : Mode) (widths : List Nat) (state : State mode) :
    (run mode (forms mode widths) state).principal.pc = state.principal.pc+Arithmetic.encodeNat mode (span widths) := by
  induction widths generalizing state with
  | nil => simp [forms,run,span,code,Arithmetic.encodeNat]
  | cons width rest ih =>
    change (run mode (forms mode rest) (execute mode (.move width) state)).principal.pc = _
    rw [ih]
    change (state.principal.pc+Arithmetic.encodeNat mode (StringPlan.opcode width).length)+Arithmetic.encodeNat mode (span rest) = _
    rw [span_cons]
    simp only [Arithmetic.encodeNat,BitVec.ofNat_add_ofNat,BitVec.add_assoc]

theorem run_source (mode : Mode) (widths : List Nat) (state : State mode) (forward : state.backwards = false) :
    (run mode (forms mode widths) state).sourceIndex = state.sourceIndex+Arithmetic.encodeNat mode widths.sum := by
  induction widths generalizing state with
  | nil => simp [forms,run,Arithmetic.encodeNat]
  | cons width rest ih =>
    change (run mode (forms mode rest) (execute mode (.move width) state)).sourceIndex = _
    rw [ih _ ((direction_preserved mode _ state).trans forward),move_effect mode width state forward]
    simp only [List.sum_cons,Arithmetic.encodeNat,BitVec.ofNat_add_ofNat,BitVec.add_assoc]

theorem run_destination (mode : Mode) (widths : List Nat) (state : State mode) (forward : state.backwards = false) :
    (run mode (forms mode widths) state).destinationIndex = state.destinationIndex+Arithmetic.encodeNat mode widths.sum := by
  induction widths generalizing state with
  | nil => simp [forms,run,Arithmetic.encodeNat]
  | cons width rest ih =>
    change (run mode (forms mode rest) (execute mode (.move width) state)).destinationIndex = _
    rw [ih _ ((direction_preserved mode _ state).trans forward),move_effect mode width state forward]
    simp only [List.sum_cons,Arithmetic.encodeNat,BitVec.ofNat_add_ofNat,BitVec.add_assoc]

theorem run_accumulator (mode : Mode) (widths : List Nat) (state : State mode) :
    (run mode (forms mode widths) state).principal.accumulator = state.principal.accumulator := by
  induction widths generalizing state with
  | nil => rfl
  | cons width rest ih => exact ih (execute mode (.move width) state)

theorem run_stack (mode : Mode) (widths : List Nat) (state : State mode) :
    (run mode (forms mode widths) state).principal.stack = state.principal.stack := by
  induction widths generalizing state with
  | nil => rfl
  | cons width rest ih => exact ih (execute mode (.move width) state)

theorem run_carry (mode : Mode) (widths : List Nat) (state : State mode) :
    (run mode (forms mode widths) state).principal.carry = state.principal.carry := by
  induction widths generalizing state with
  | nil => rfl
  | cons width rest ih => exact ih (execute mode (.move width) state)

/-- The selected SI/DI word execution refines the proved snapshot copy for
arbitrary finite element sequences under static nonoverlap/capacity conditions. -/
theorem effect (mode : Mode) (widths : List Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (separate : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat widths.sum) :
    (run mode (forms mode widths) state).principal.memory = ByteMemory.putBytes state.principal.memory state.destinationIndex.toNat
      (ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat widths.sum) := by
  have simulation := run_view mode widths state forward sourceFits destinationFits
  rw [StringCopy.effect widths (view mode state) separate] at simulation
  exact congrArg StringCopy.State.memory simulation

theorem copied (mode : Mode) (widths : List Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (separate : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat widths.sum) :
    ByteMemory.bytesAt (run mode (forms mode widths) state).principal.memory state.destinationIndex.toNat widths.sum =
      ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat widths.sum := by
  rw [effect mode widths state forward sourceFits destinationFits separate]
  simpa only [ByteMemory.bytes_at_length] using ByteMemory.bytes_at_put state.principal.memory state.destinationIndex.toNat
    (ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat widths.sum)

theorem frame (mode : Mode) (widths : List Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (separate : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat widths.sum) (position : Nat)
    (outside : ¬ByteMemory.Inside state.destinationIndex.toNat widths.sum position) :
    (run mode (forms mode widths) state).principal.memory position = state.principal.memory position := by
  rw [effect mode widths state forward sourceFits destinationFits separate]
  exact ByteMemory.put_frame _ _ _ _ (by simpa only [ByteMemory.bytes_at_length] using outside)

end SmcTuring.Native.StringMoves
