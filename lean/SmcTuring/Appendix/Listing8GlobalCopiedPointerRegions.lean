module
public import SmcTuring.Appendix.Listing8GlobalStoreSubregions
public import SmcTuring.Appendix.Listing8CopiedPointerWrites
public import SmcTuring.Native.StringStoreTemplateRuns

public section
namespace SmcTuring.Appendix.Listing8GlobalCopiedPointerRegions
open Native Listing8Prototypes Listing8CopiedPointer

theorem field (mode : Mode) (origin source copied : Nat)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourceRegion : Listing8GlobalControlLayout.Allowed mode origin source (pointerSpan mode))
    (copiedRegion : Listing8GlobalControlLayout.Allowed mode origin copied (pointerSpan mode)) :
    Listing8GlobalControlLayout.Allowed mode origin (label mode source copied).toNat mode.wordBytes := by
  have fits : selfField mode source copied<2^(8*mode.wordBytes) := by
    cases mode <;> simp [selfField,pointerField,Listing8CopiedPointer.origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize]
      at sourceFits copiedFits ⊢ <;> omega
  change Listing8GlobalControlLayout.Allowed mode origin (Arithmetic.encodeNat mode (selfField mode source copied)).toNat mode.wordBytes
  rw [Arithmetic.encode_nat_toNat mode _ fits]
  cases mode with
  | x86 =>
    apply Listing8GlobalStoreSubregions.within .x86 origin _ _ _ _ sourceRegion
    all_goals simp [selfField,pointerField,Listing8CopiedPointer.origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes]
  | x64 =>
    apply Listing8GlobalStoreSubregions.within .x64 origin _ _ _ _ copiedRegion
    all_goals simp [selfField,pointerField,Listing8CopiedPointer.origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes]

theorem regions (mode : Mode) (origin source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes)) (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourceRegion : Listing8GlobalControlLayout.Allowed mode origin source (pointerSpan mode))
    (copiedRegion : Listing8GlobalControlLayout.Allowed mode origin copied (pointerSpan mode))
    (target : Listing8GlobalControlLayout.Allowed mode origin value.toNat mode.wordBytes)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length=pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length=pointerBytes mode source value) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((forms mode source copied value).map (StringWrites.liftString mode)) state := by
  have pointer:=self_value mode source copied value state.principal.memory sourceFits copiedFits sourceCurrent copiedCurrent
  have writes:=Reader.four_writes_owned mode state.principal (label mode source copied)
    (ReaderImage.firstDisp mode (Listing8CopiedPointer.origin mode source copied)) (ReaderImage.secondDisp mode)
    (first_hits mode source copied state.principal entry) (second_hits mode source copied state.principal entry)
    (fun address => Listing8GlobalControlLayout.Allowed mode origin address.toNat mode.wordBytes)
    (field mode origin source copied sourceFits copiedFits sourceRegion copiedRegion) (by rw [pointer];exact target)
  have actual : Writes.OwnedRun mode (fun address => Listing8GlobalControlLayout.Allowed mode origin address.toNat mode.wordBytes)
      [first mode source copied,second mode source copied,.exchangeIndirect,.moffs value] state.principal := by
    rw [←pointer]
    simpa only [Writes.OwnedRun,and_true,first,second,Reader.swapped,Reader.restored,Reader.dereferenced] using writes
  have lifted:=StringStoreTemplateRuns.native mode (Listing8GlobalControlLayout.Allowed mode origin) _ state actual
  simpa only [forms,List.map_cons,List.map_nil,StringWrites.liftNative] using lifted

end SmcTuring.Appendix.Listing8GlobalCopiedPointerRegions
