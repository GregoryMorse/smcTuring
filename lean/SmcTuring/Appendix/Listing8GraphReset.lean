module
public import SmcTuring.Appendix.Listing8GraphLayout

public section
namespace SmcTuring.Appendix.Listing8GraphReset
open Native Listing8Prototypes

/-- The printed reset after every original transition declaration. -/
@[expose] def region (mode : Mode) (origin transitions : Nat) : Listing8ResetLayout.Layout :=
  ⟨Listing8GraphLayout.reset mode origin transitions,
    origin+(if mode=.x86 then 801 else 1269),origin+(if mode=.x86 then 21 else 61),
    origin+(if mode=.x86 then 712 else 1154),origin+(if mode=.x86 then 58 else 116),
    origin+(if mode=.x86 then 129 else 230),Listing8FullTableImage.start mode origin⟩

theorem endpoint (mode : Mode) (origin transitions : Nat) :
    Listing8ResetLayout.endPC mode (region mode origin transitions)=
      Listing8GraphLayout.input mode origin transitions := by
  rw [(Listing8ResetLayout.positions mode (region mode origin transitions)).2.2.2]
  rfl

theorem capacity (mode : Mode) (origin transitions nodes : Nat)
    (bounds : Listing8GraphLayout.Bounds mode origin transitions nodes) :
    Listing8ResetLayout.endPC mode (region mode origin transitions)<2^(8*mode.wordBytes) := by
  rw [endpoint]
  exact Nat.lt_of_le_of_lt (Listing8GraphLayout.node_lower mode origin transitions nodes) bounds.capacity

/-- Every reset relocation and complete-word separation follows from the
packed graph endpoint and its bounded x64 reset distance. -/
theorem valid (mode : Mode) (origin transitions nodes : Nat)
    (bounds : Listing8GraphLayout.Bounds mode origin transitions nodes) :
    Listing8ResetLayout.Bounds mode (region mode origin transitions) := by
  have cap:=capacity mode origin transitions nodes bounds
  have reach:=bounds.resetReach
  cases mode
  all_goals refine ⟨cap,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try apply ConversionLayout.Admissible.mk
  all_goals try (intro only;cases only)
  all_goals simp only [Listing8ResetLayout.endPC,Listing8ResetLayout.markerPC,Listing8ResetLayout.transitionCopy,
    Listing8ResetLayout.ownerPC,Listing8ResetLayout.inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,
    ConversionLayout.secondPC,ConversionLayout.exchangeSize,ConversionLayout.storeSize,StringInit.field,
    StringCodec.initialSize,StringCodec.fieldOffset,Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,
    wordPrefix,Mode.wordBytes,Relocation.SignedDelta,Relocation.delta,region,Listing8GraphLayout.input,
    Listing8GraphLayout.reset,Listing8GraphLayout.transition,Listing8FullTableImage.start,
    Listing8FailLayout.end_offset,
    transitionSpan,pointerSpan,ReaderImage.totalSize,reduceCtorEq,ite_true,ite_false,true_implies,false_implies,
    List.length_nil,List.length_cons] at cap reach ⊢
  all_goals omega

theorem actual_region (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout)
    (t : Listing8PointerCopies.Targets) (sentinel : Nat) (table : List (Listing8CopyImage.Values mode))
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing8TableResetImage.region mode origin l sentinel table=region mode origin table.length := by
  have failure:=Listing8FailureGeometry.positions mode l t sentinel (Listing8BootImage.beginPC mode origin) body
  have input:=Listing8InputBounds.positions mode l t body.state.head.input.fields body.state.head.input.joined
  have second:=(Listing8Initializer.code_geometry mode l).1
  have saved : Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel)=
      origin+(if mode=.x86 then 712 else 1154) := by
    change (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin)).start+10+StringCodec.fieldOffset mode=_
    rw [failure.1,boot.packed]
    cases mode <;> rfl
  have cursor : l.input.cursor=origin+(if mode=.x86 then 58 else 116) := by
    rw [input.2.2,boot.packed]
    cases mode <;> rfl
  have transitionCursor : (Listing8StateGeometry.region mode l).cursor=origin+(if mode=.x86 then 129 else 230) := by
    change StringCodec.sourceField mode (Listing8CopyImage.secondStart mode l)=_
    rw [second,boot.packed]
    cases mode <;> rfl
  unfold Listing8TableResetImage.region region
  rw [saved,cursor,transitionCursor,(Listing8JumpLayout.positions mode origin).1]
  cases mode <;> rfl

theorem actual_valid (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout)
    (t : Listing8PointerCopies.Targets) (sentinel nodes : Nat) (table : List (Listing8CopyImage.Values mode))
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8GraphLayout.Bounds mode origin table.length nodes) :
    Listing8ResetLayout.Bounds mode (Listing8TableResetImage.region mode origin l sentinel table) := by
  rw [actual_region mode origin l t sentinel table boot body]
  exact valid mode origin table.length nodes bounds

end SmcTuring.Appendix.Listing8GraphReset
