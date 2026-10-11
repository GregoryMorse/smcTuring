module
public import SmcTuring.Appendix.Listing8CopiedPointer
public import SmcTuring.Native.StringFieldWrites

public section
namespace SmcTuring.Appendix.Listing8CopiedPointerWrites
open Native Listing8Prototypes Listing8CopiedPointer

theorem field (mode : Mode) (codeStart codeEnd source copied : Nat)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourceInside : codeStart≤source ∧ source+pointerSpan mode≤codeEnd)
    (copiedInside : codeStart≤copied ∧ copied+pointerSpan mode≤codeEnd) :
    StringWrites.WordOwned mode codeStart codeEnd (label mode source copied) := by
  change StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (selfField mode source copied))
  apply StringFieldWrites.word_owned
  · cases mode <;> simp [selfField,pointerField,origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize] at * <;> omega
  · cases mode <;> simp [selfField,pointerField,origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes] at * <;> constructor <;> omega

/-- Present original and copied bytes determine the reader's indirect
target. x86 owns the original operand; x64 owns the relocated copied one. -/
theorem owned (mode : Mode) (codeStart codeEnd source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourceInside : codeStart≤source ∧ source+pointerSpan mode≤codeEnd)
    (copiedInside : codeStart≤copied ∧ copied+pointerSpan mode≤codeEnd)
    (targetInside : codeStart≤value.toNat ∧ value.toNat+mode.wordBytes≤codeEnd)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length=pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length=pointerBytes mode source value) :
    StringWrites.OwnedRun mode codeStart codeEnd ((forms mode source copied value).map (StringWrites.liftString mode)) state := by
  have pointer:=self_value mode source copied value state.principal.memory sourceFits copiedFits sourceCurrent copiedCurrent
  have fields:=Reader.four_writes_owned mode state.principal (label mode source copied)
    (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)
    (first_hits mode source copied state.principal entry) (second_hits mode source copied state.principal entry)
    (StringWrites.WordOwned mode codeStart codeEnd) (field mode codeStart codeEnd source copied sourceFits copiedFits sourceInside copiedInside)
    (by rw [pointer];exact targetInside)
  have actual : Writes.OwnedRun mode (StringWrites.WordOwned mode codeStart codeEnd)
      [first mode source copied,second mode source copied,.exchangeIndirect,.moffs value] state.principal := by
    rw [←pointer]
    simpa only [Writes.OwnedRun,and_true,first,second,Reader.swapped,Reader.restored,Reader.dereferenced] using fields
  have lifted:=StringWrites.native_owned_run mode codeStart codeEnd _ state actual
  simpa only [forms,List.map_cons,List.map_nil,StringWrites.liftNative] using lifted

end SmcTuring.Appendix.Listing8CopiedPointerWrites
