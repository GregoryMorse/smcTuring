module
public import SmcTuring.Appendix.Listing8PointerTemplate
public import SmcTuring.Appendix.Listing8OriginalPointer
public import SmcTuring.Native.StringTemplateStates

public section
namespace SmcTuring.Appendix.Listing8OriginalPointerTemplates
open Native Listing8Prototypes Listing8CopiedPointer

/-- Original and copied DEFADDR retain all their static instruction templates
at every reached boundary. The original x86 operand may be outside its copy;
x64 modifies the copied operand. Temporary values are unrestricted words. -/
theorem run (mode : Mode) (source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourcePlaced : source=copied ∨ source+pointerSpan mode≤copied ∨ copied+pointerSpan mode≤source)
    (targetOutside : value.toNat+mode.wordBytes≤copied ∨ copied+pointerSpan mode≤value.toNat)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length=pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length=pointerBytes mode source value) :
    StringTemplateStates.Run mode
      (fun reached => Listing8PointerTemplate.Intact mode source copied reached.principal.memory)
      ((forms mode source copied value).map (StringWrites.liftString mode)) state := by
  let one := StringExecution.execute mode (.native (first mode source copied)) state
  let two := StringExecution.execute mode (.native (second mode source copied)) one
  let three := StringExecution.execute mode (.native .exchangeIndirect) two
  let four := StringExecution.execute mode (.native (.moffs value)) three
  have initial := Listing8PointerTemplate.initial mode source copied value state.principal.memory copiedCurrent
  have pointer := self_value mode source copied value state.principal.memory sourceFits copiedFits sourceCurrent copiedCurrent
  have firstHits := first_hits mode source copied state.principal entry
  have secondHits := second_hits mode source copied state.principal entry
  have fieldFits : selfField mode source copied<2^(8*mode.wordBytes) := by
    cases mode <;> simp [selfField,pointerField,origin,Mode.wordBytes,
      pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset] at * <;> omega
  have mem1 : one.principal.memory=ByteMemory.putWord mode state.principal.memory
      (selfField mode source copied) state.principal.accumulator := by
    have e := congrArg Execution.State.memory (Reader.exchange_effect mode state.principal
      (label mode source copied) _ firstHits)
    change one.principal.memory=ByteMemory.putWord mode state.principal.memory
      (Arithmetic.encodeNat mode (selfField mode source copied)).toNat state.principal.accumulator at e
    rw [Arithmetic.encode_nat_toNat mode _ fieldFits] at e
    exact e
  have mem2 : two.principal.memory=state.principal.memory :=
    Reader.restored_memory mode state.principal _ _ _ firstHits secondHits
  have mem3 : three.principal.memory=ByteMemory.putWord mode state.principal.memory value.toNat value := by
    have e := Reader.dereferenced_memory mode state.principal _ _ _ firstHits secondHits
    rw [pointer] at e
    exact e
  have mem4 : four.principal.memory=state.principal.memory := by
    change (finish mode source copied value state).principal.memory=state.principal.memory
    rw [effect mode source copied value state entry pointer]
  have kept1 : Listing8PointerTemplate.Intact mode source copied one.principal.memory := by
    rw [mem1]
    cases mode with
    | x86 =>
      rcases sourcePlaced with same | apart
      · subst source
        apply Listing8PointerTemplate.operand_store .x86 copied copied state.principal.memory initial
          (selfField .x86 copied copied) (LittleEndian.wordEncode 4 state.principal.accumulator)
        · exact Nat.le_refl _
        · change copied+14+(LittleEndian.wordEncode 4 state.principal.accumulator).length≤copied+18
          rw [LittleEndian.word_encode_length 4 state.principal.accumulator]
          omega
      · apply Listing8PointerTemplate.frame .x86 source copied state.principal.memory initial
          (selfField .x86 source copied) (LittleEndian.wordEncode 4 state.principal.accumulator)
        change source+14+(LittleEndian.wordEncode 4 state.principal.accumulator).length≤copied ∨ copied+18≤source+14
        rw [LittleEndian.word_encode_length 4 state.principal.accumulator]
        change source+18≤copied ∨ copied+18≤source at apart
        rcases apart with before | after
        · left;omega
        · right;omega
    | x64 =>
      apply Listing8PointerTemplate.operand_store .x64 source copied state.principal.memory initial
        (selfField .x64 source copied) (LittleEndian.wordEncode 8 state.principal.accumulator)
      · exact Nat.le_refl _
      · change copied+19+(LittleEndian.wordEncode 8 state.principal.accumulator).length≤copied+27
        rw [LittleEndian.word_encode_length 8 state.principal.accumulator]
        omega
  have kept2 : Listing8PointerTemplate.Intact mode source copied two.principal.memory := by rw [mem2];exact initial
  have kept3 : Listing8PointerTemplate.Intact mode source copied three.principal.memory := by
    rw [mem3]
    apply Listing8PointerTemplate.frame mode source copied state.principal.memory initial
    simpa only [LittleEndian.word_encode_length] using targetOutside
  have kept4 : Listing8PointerTemplate.Intact mode source copied four.principal.memory := by rw [mem4];exact initial
  change Listing8PointerTemplate.Intact mode source copied state.principal.memory ∧
    Listing8PointerTemplate.Intact mode source copied one.principal.memory ∧
    Listing8PointerTemplate.Intact mode source copied two.principal.memory ∧
    Listing8PointerTemplate.Intact mode source copied three.principal.memory ∧
    Listing8PointerTemplate.Intact mode source copied four.principal.memory
  exact ⟨initial,kept1,kept2,kept3,kept4⟩

theorem original (mode : Mode) (pc : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (fits : pc+pointerSpan mode<2^(8*mode.wordBytes))
    (targetOutside : value.toNat+mode.wordBytes≤pc ∨ pc+pointerSpan mode≤value.toNat)
    (packet : ByteMemory.bytesAt state.principal.memory pc (pointerBytes mode pc value).length=pointerBytes mode pc value) :
    StringTemplateStates.Run mode
      (fun reached => Listing8PointerTemplate.Intact mode pc pc reached.principal.memory)
      ((forms mode pc pc value).map (StringWrites.liftString mode)) state :=
  run mode pc pc value state entry fits fits (Or.inl rfl) targetOutside packet packet

/-- Current decoding at all four static boundaries is available at every
actual prefix of the helper, even when that boundary is not the next PC. -/
theorem prefix_decodes (mode : Mode) (source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourcePlaced : source=copied ∨ source+pointerSpan mode≤copied ∨ copied+pointerSpan mode≤source)
    (targetOutside : value.toNat+mode.wordBytes≤copied ∨ copied+pointerSpan mode≤value.toNat)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length=pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length=pointerBytes mode source value)
    (before after : List (StringStack.Form mode))
    (cut : (forms mode source copied value).map (StringWrites.liftString mode)=before++after) :
    let reached := StringWrites.run mode before state
    let live := Protected.wordAt mode reached.principal.memory (pointerField mode copied)
    StringStack.fetch mode reached.principal.memory copied=some (StringWrites.liftNative mode (first mode source copied)) ∧
    StringStack.fetch mode reached.principal.memory (copied+ReaderImage.firstSize mode)=
      some (StringWrites.liftNative mode (second mode source copied)) ∧
    StringStack.fetch mode reached.principal.memory (copied+ReaderImage.firstSize mode+ReaderImage.secondSize mode)=
      some (StringWrites.liftNative mode .exchangeIndirect) ∧
    StringStack.fetch mode reached.principal.memory (copied+ReaderImage.prefixSize mode)=
      some (StringWrites.liftNative mode (.moffs live)) := by
  have allStates := run mode source copied value state entry sourceFits copiedFits sourcePlaced targetOutside sourceCurrent copiedCurrent
  rw [cut] at allStates
  exact Listing8PointerTemplate.decodes mode source copied _ (StringTemplateStates.at_prefix mode _ before after state allStates)

end SmcTuring.Appendix.Listing8OriginalPointerTemplates
