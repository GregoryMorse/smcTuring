module
public import SmcTuring.Native.StringMoves

public section
namespace SmcTuring.Native.StringMoveTrace
open StringExecution StringMoves

/-- The full destination interval lies outside the complete MOVS body. The
source may be code; source/destination disjointness is needed for the snapshot
copy result, while this condition alone keeps all future packet bytes intact. -/
@[expose] def CodeSeparate (start : Nat) (widths : List Nat) (destination : Nat) : Prop :=
  destination+widths.sum ≤ start ∨ start+span widths ≤ destination

theorem current_head (memory : ByteMemory.Memory) (start width : Nat) (rest : List Nat)
    (current : ByteMemory.bytesAt memory start (span (width::rest)) = code (width::rest)) :
    ByteMemory.bytesAt memory start (StringPlan.opcode width).length = StringPlan.opcode width := by
  rw [←Fetch.bytes_at_take memory start (span (width::rest)) _ (by rw [span_cons]; omega),current,code_cons]
  simp

theorem current_tail (memory : ByteMemory.Memory) (start width : Nat) (rest : List Nat)
    (current : ByteMemory.bytesAt memory start (span (width::rest)) = code (width::rest)) :
    ByteMemory.bytesAt memory (start+(StringPlan.opcode width).length) (span rest) = code rest := by
  have head := current_head memory start width rest current
  rw [span_cons,Protected.bytes_at_append,code_cons,head] at current
  simpa using current

theorem tail_separate (start width destination : Nat) (rest : List Nat)
    (separate : CodeSeparate start (width::rest) destination) :
    CodeSeparate (start+(StringPlan.opcode width).length) rest (destination+width) := by
  unfold CodeSeparate at *
  rw [span_cons,List.sum_cons] at separate
  rcases separate with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem next_location (mode : Mode) (state : State mode) (start width : Nat)
    (location : state.principal.pc = Arithmetic.encodeNat mode start) :
    (execute mode (.move width) state).principal.pc = Arithmetic.encodeNat mode (start+(StringPlan.opcode width).length) := by
  change state.principal.pc+Arithmetic.encodeNat mode (StringPlan.opcode width).length = _
  rw [location]
  exact BitVec.ofNat_add_ofNat _ _

/-- Construct every fetch from the initialized body and prove its preservation
after each actual store. Lengths and boundaries are inferred by the live decoder;
no intermediate trace, future fetch or future image invariant is assumed. -/
theorem constructed_trace (mode : Mode) (widths : List Nat) (start : Nat) (state : State mode)
    (legal : ∀ width ∈ widths, StringPlan.Legal mode width)
    (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (codeFits : start+span widths < 2^(8*mode.wordBytes))
    (separate : CodeSeparate start widths state.destinationIndex.toNat)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (current : ByteMemory.bytesAt state.principal.memory start (span widths) = code widths) :
    Trace mode state (forms mode widths) (run mode (forms mode widths) state) := by
  induction widths generalizing start state with
  | nil => exact .nil state
  | cons width rest ih =>
    have startFits : start < 2^(8*mode.wordBytes) := by omega
    have fetched : StringForm.fetch mode state.principal.memory state.principal.pc.toNat = some (.move width) := by
      rw [location,Arithmetic.encode_nat_toNat mode start startFits]
      exact StringForm.fetch_current_encoding mode _ start (.move width) (legal _ (by simp))
        (current_head state.principal.memory start width rest current)
    have sourceHead : state.sourceIndex.toNat+width < 2^(8*mode.wordBytes) := by
      simp only [List.sum_cons] at sourceFits; omega
    have destinationHead : state.destinationIndex.toNat+width < 2^(8*mode.wordBytes) := by
      simp only [List.sum_cons] at destinationFits; omega
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
    have tailFits : start+(StringPlan.opcode width).length+span rest < 2^(8*mode.wordBytes) := by
      simpa only [span_cons,Nat.add_assoc] using codeFits
    have tailSeparate : CodeSeparate (start+(StringPlan.opcode width).length) rest
        (execute mode (.move width) state).destinationIndex.toNat := by
      rw [destinationNext]
      exact tail_separate start width _ rest separate
    have tailCurrent : ByteMemory.bytesAt (execute mode (.move width) state).principal.memory
        (start+(StringPlan.opcode width).length) (span rest) = code rest := by
      rw [move_effect mode width state forward]
      change ByteMemory.bytesAt (ByteMemory.putBytes state.principal.memory state.destinationIndex.toNat
        (ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat width)) _ _ = _
      rw [ByteMemory.bytes_at_frame]
      · exact current_tail state.principal.memory start width rest current
      · intro index
        have bound := index.isLt
        simp only [ByteMemory.bytes_at_length,ByteMemory.Inside]
        unfold CodeSeparate at separate
        rw [span_cons,List.sum_cons] at separate
        rcases separate with before | after <;> omega
    exact .step fetched (ih _ _ (fun next member => legal next (by simp [member]))
      ((direction_preserved mode _ state).trans forward) sourceTail destinationTail tailFits tailSeparate
      (next_location mode state start width location) tailCurrent)

theorem image_trace (mode : Mode) (widths : List Nat) (start : Nat) (backing : ByteMemory.Memory) (state : State mode)
    (legal : ∀ width ∈ widths, StringPlan.Legal mode width) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (codeFits : start+span widths < 2^(8*mode.wordBytes))
    (separate : CodeSeparate start widths state.destinationIndex.toNat)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (initialized : state.principal.memory = ByteMemory.putBytes backing start (code widths)) :
    Trace mode state (forms mode widths) (run mode (forms mode widths) state) := by
  apply constructed_trace mode widths start state legal forward sourceFits destinationFits codeFits separate location
  rw [initialized]
  exact ByteMemory.bytes_at_put backing start (code widths)

/-- Positive Listing 5 body contract, including actual-byte fetch, exact
snapshot copy, full SI/DI advance, PC endpoint and unchanged AX/SP/CF/DF. -/
theorem correct (mode : Mode) (size start : Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+size < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+size < 2^(8*mode.wordBytes))
    (codeFits : start+span (StringPlan.widths mode size) < 2^(8*mode.wordBytes))
    (copySeparate : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat size)
    (codeSeparate : CodeSeparate start (StringPlan.widths mode size) state.destinationIndex.toNat)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (current : ByteMemory.bytesAt state.principal.memory start (span (StringPlan.widths mode size)) = StringPlan.bytes mode size) :
    let finish := run mode (forms mode (StringPlan.widths mode size)) state
    Trace mode state (forms mode (StringPlan.widths mode size)) finish ∧
    finish.principal.memory = ByteMemory.putBytes state.principal.memory state.destinationIndex.toNat
      (ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat size) ∧
    finish.sourceIndex = state.sourceIndex+Arithmetic.encodeNat mode size ∧
    finish.destinationIndex = state.destinationIndex+Arithmetic.encodeNat mode size ∧
    finish.principal.pc = Arithmetic.encodeNat mode (start+span (StringPlan.widths mode size)) ∧
    finish.principal.accumulator = state.principal.accumulator ∧
    finish.principal.stack = state.principal.stack ∧
    finish.principal.carry = state.principal.carry ∧ finish.backwards = false := by
  have total : (StringPlan.widths mode size).sum = size := StringPlan.total mode size
  refine ⟨constructed_trace mode _ start state (StringPlan.legal mode size) forward (by rwa [total]) (by rwa [total])
    codeFits codeSeparate location current,?_,?_,?_,?_,run_accumulator mode _ state,run_stack mode _ state,run_carry mode _ state,?_⟩
  · simpa only [total] using effect mode (StringPlan.widths mode size) state forward (by rwa [total]) (by rwa [total]) (by rwa [total])
  · simpa only [total] using run_source mode (StringPlan.widths mode size) state forward
  · simpa only [total] using run_destination mode (StringPlan.widths mode size) state forward
  · rw [run_pc,location]; exact BitVec.ofNat_add_ofNat _ _
  · exact (run_direction mode _ state).trans forward

theorem code_preserved (mode : Mode) (widths : List Nat) (start : Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (copySeparate : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat widths.sum)
    (codeSeparate : CodeSeparate start widths state.destinationIndex.toNat) :
    ByteMemory.bytesAt (run mode (forms mode widths) state).principal.memory start (span widths) =
      ByteMemory.bytesAt state.principal.memory start (span widths) := by
  rw [effect mode widths state forward sourceFits destinationFits copySeparate]
  apply ByteMemory.bytes_at_frame
  intro index
  have bound := index.isLt
  simp only [ByteMemory.bytes_at_length,ByteMemory.Inside]
  unfold CodeSeparate at codeSeparate
  rcases codeSeparate with before | after <;> omega

end SmcTuring.Native.StringMoveTrace
