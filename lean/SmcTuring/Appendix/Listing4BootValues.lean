module
public import SmcTuring.Appendix.Listing4Boot

public section
namespace SmcTuring.Appendix.Listing4BootValues
open Native Listing4StackLayout Listing4JumpLayout
@[expose] def result (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :=
  Listing4JumpEffects.finish mode start (Listing4Boot.initial mode start seed)

theorem effect (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+Listing4Boot.size mode < 2^(8*mode.wordBytes)) :
    result mode start seed = {Listing4Boot.initial mode start seed with principal :=
      {(Listing4Boot.initial mode start seed).principal with
        pc := Arithmetic.encodeNat mode (beginPC mode start)
        accumulator := Listing4StackInit.accumulator mode start (Listing4Boot.initial mode start seed)
        stack := Arithmetic.encodeNat mode (returnField mode start)
        carry := Listing4JumpEffects.flag mode start (Listing4Boot.initial mode start seed)
        memory := ByteMemory.putWord mode
          (ByteMemory.putWord mode (Listing4Boot.initial mode start seed).principal.memory (stptr mode start) seed.principal.stack)
          (returnField mode start) (Arithmetic.encodeNat mode (beginPC mode start))}} := by
  exact Listing4JumpEffects.called_effect mode start _ rfl (by rw [Listing4Boot.endpoint];exact fits)
    (Listing4Boot.stack_packet mode start _ (Listing4Boot.initial_current mode start seed))

theorem endpoint (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+Listing4Boot.size mode < 2^(8*mode.wordBytes)) :
    (result mode start seed).principal.pc.toNat = start+Listing4Boot.size mode := by
  rw [effect mode start seed fits,Listing4Boot.endpoint,Arithmetic.encode_nat_toNat mode _ fits]

theorem stack (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+Listing4Boot.size mode < 2^(8*mode.wordBytes)) :
    (result mode start seed).principal.stack = Arithmetic.encodeNat mode (returnField mode start) := by
  rw [effect mode start seed fits]

theorem return_word (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+Listing4Boot.size mode < 2^(8*mode.wordBytes)) :
    MixedMemory.getWord mode (result mode start seed).principal.memory (returnField mode start) =
      Arithmetic.encodeNat mode (beginPC mode start) := by
  rw [effect mode start seed fits,MixedMemory.get_put]

theorem saved_stack (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+Listing4Boot.size mode < 2^(8*mode.wordBytes)) :
    MixedMemory.getWord mode (result mode start seed).principal.memory (stptr mode start) = seed.principal.stack := by
  rw [effect mode start seed fits,MixedFrames.word_after_word mode _ (returnField mode start) (stptr mode start) _ (fields_separate mode start),
    MixedMemory.get_put]

theorem registers (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+Listing4Boot.size mode < 2^(8*mode.wordBytes)) :
    (result mode start seed).principal.accumulator = Listing4StackInit.accumulator mode start seed ∧
    (result mode start seed).sourceIndex = seed.sourceIndex ∧
    (result mode start seed).destinationIndex = seed.destinationIndex ∧
    (result mode start seed).backwards = seed.backwards ∧
    (result mode start seed).principal.carry = Listing4JumpEffects.flag mode start seed := by
  rw [effect mode start seed fits]
  cases mode <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- CALL preserves every later packet; the two full-word writes stay in the
already executed DEFSTACK code operands. The target continuation is next. -/
theorem later_window (mode : Mode) (start : Nat) (seed : StringExecution.State mode) (observed count : Nat)
    (fits : start+Listing4Boot.size mode < 2^(8*mode.wordBytes))
    (later : jumpPC mode start ≤ observed) :
    ByteMemory.bytesAt (result mode start seed).principal.memory observed count =
      ByteMemory.bytesAt (Listing4Boot.initial mode start seed).principal.memory observed count := by
  rw [effect mode start seed fits,StackWindows.word_window mode _ (returnField mode start) observed count _
    (Or.inl (Nat.le_trans (Listing4Boot.return_before_jump mode start) later)),
    StackWindows.word_window mode _ (stptr mode start) observed count _
    (Or.inl (Nat.le_trans (Listing4Boot.stack_before_jump mode start) later))]
end SmcTuring.Appendix.Listing4BootValues
