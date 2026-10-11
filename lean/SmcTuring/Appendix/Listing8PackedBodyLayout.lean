module
public import SmcTuring.Appendix.Listing8GraphInputContext
public import SmcTuring.Appendix.Listing9PackedLayout

public section
namespace SmcTuring.Appendix.Listing8PackedBodyLayout
open Native Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def main (mode : Mode) (origin : Nat) := Listing4EntryLayout.mainPC mode origin
/-- Literal offsets are checked below against the preserved packed encoders. -/
@[expose] def input (mode : Mode) (origin head : Nat) : Listing8LiteralInput.Layout :=
  ⟨main mode origin+(if mode=.x86 then 367 else 550),StringCodec.sourceField mode (main mode origin),head,
   main mode origin+(if mode=.x86 then 630 else 994),main mode origin+(if mode=.x86 then 583 else 898)⟩
@[expose] def layout (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) : Listing8CopyImage.Layout :=
  ⟨main mode origin,nodePC mode origin g node,rulePC mode origin g rule,
   input mode origin (nodePC mode origin g node),main mode origin+(if mode=.x86 then 587 else 912)⟩
@[expose] def targets (mode : Mode) (origin : Nat) : Targets :=
  ⟨main mode origin+(if mode=.x86 then 614 else 968),main mode origin+(if mode=.x86 then 523 else 784),
   main mode origin+(if mode=.x86 then 539 else 816)⟩

theorem labels (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (layout mode origin g node rule).start=Listing4EntryLayout.mainPC mode origin ∧
    (layout mode origin g node rule).sourceNode=nodePC mode origin g node ∧
    (layout mode origin g node rule).sourceTransition=rulePC mode origin g rule ∧
    (layout mode origin g node rule).input.cursor=StringCodec.sourceField mode (layout mode origin g node rule).start ∧
    (layout mode origin g node rule).input.head=(layout mode origin g node rule).sourceNode := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem joined (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (layout mode origin g node rule).input.start=Listing8PointerCopies.endPC mode (layout mode origin g node rule) := by
  rw [(Listing8PointerCopies.sizes mode (layout mode origin g node rule) (targets mode origin)).2.1,
    (Listing8Initializer.code_geometry mode (layout mode origin g node rule)).2.2]
  cases mode <;> rfl

theorem input_end (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8LiteralInput.endPC mode (layout mode origin g node rule).input=main mode origin+(if mode=.x86 then 506 else 730) := by
  have ending:=(Listing8LiteralInput.positions mode (layout mode origin g node rule).input).2.2.2.2.2.2.2
  rw [ending]
  cases mode <;> rfl

theorem direction_region (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8DirectionGeometry.region mode (layout mode origin g node rule)=
      ⟨main mode origin+(if mode=.x86 then 506 else 730),StringCodec.sourceField mode (main mode origin)⟩ := by
  unfold Listing8DirectionGeometry.region
  rw [input_end]
  rfl

theorem direction_labels (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (layout mode origin g node rule).direction=Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode (layout mode origin g node rule)) ∧
    (targets mode origin).back=Listing8DirectionLayout.backPC mode (Listing8DirectionGeometry.region mode (layout mode origin g node rule)) ∧
    (targets mode origin).forward=Listing8DirectionLayout.forwardPC mode (Listing8DirectionGeometry.region mode (layout mode origin g node rule)) ∧
    (layout mode origin g node rule).input.directionMask=Listing8DirectionLayout.maskPC mode (Listing8DirectionGeometry.region mode (layout mode origin g node rule))+6 ∧
    Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode (layout mode origin g node rule))=main mode origin+(if mode=.x86 then 597 else 932) := by
  rw [direction_region]
  cases mode <;> simp [layout,input,targets,Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,
    Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,
    Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem state_region (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8StateGeometry.region mode (layout mode origin g node rule)=
      ⟨main mode origin+(if mode=.x86 then 597 else 932),StringCodec.sourceField mode (main mode origin+(if mode=.x86 then 71 else 114))⟩ := by
  unfold Listing8StateGeometry.region
  rw [(direction_labels mode origin g node rule).2.2.2.2,(Listing8Initializer.code_geometry mode (layout mode origin g node rule)).1]
  rfl

theorem state_labels (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (targets mode origin).state=Listing8StateLayout.newPC mode (Listing8StateGeometry.region mode (layout mode origin g node rule)) ∧
    (layout mode origin g node rule).input.transitionMask=Listing8StateLayout.maskPC mode (Listing8StateGeometry.region mode (layout mode origin g node rule))+6 ∧
    Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode (layout mode origin g node rule))=main mode origin+(if mode=.x86 then 644 else 1028) := by
  rw [state_region]
  cases mode <;> simp [layout,input,targets,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,
    Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem failure_region (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (sentinel begin : Nat) :
    Listing8FailureGeometry.region mode (layout mode origin g node rule) sentinel begin=
      ⟨main mode origin+(if mode=.x86 then 644 else 1028),StringCodec.sourceField mode (main mode origin+(if mode=.x86 then 71 else 114)),sentinel,begin⟩ := by
  unfold Listing8FailureGeometry.region
  rw [(state_labels mode origin g node rule).2.2,state_region]

theorem failure_end (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (sentinel begin : Nat) :
    Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode (layout mode origin g node rule) sentinel begin)+5=
      main mode origin+(if mode=.x86 then 754 else 1177) := by
  rw [failure_region]
  cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan,Listing8FailureLayout.endPC,
    Listing8FailureLayout.xorPC,Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,Listing8FailureLayout.notPC,
    Listing8FailureLayout.comparisonPC,Listing8FailureLayout.ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Nat.add_assoc]

/-- Every fixed body fragment ends before the first original transition. -/
theorem before_table (mode : Mode) (origin : Nat) :
    main mode origin+(if mode=.x86 then 754 else 1177)≤Listing8FullTableImage.start mode origin := by
  rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset]
  cases mode <;> dsimp [main,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega

theorem copy_positions (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (Listing8CopyImage.nodeParams mode (layout mode origin g node rule)).destination=main mode origin+(if mode=.x86 then 187 else 273) ∧
    (Listing8CopyImage.transitionParams mode (layout mode origin g node rule)).destination=main mode origin+(if mode=.x86 then 233 else 337) ∧
    Listing8CopyImage.codeEnd mode (layout mode origin g node rule)=main mode origin+(if mode=.x86 then 299 else 421) := by
  have copied:=Listing8Initializer.code_geometry mode (layout mode origin g node rule)
  refine ⟨?_,?_,copied.2.2⟩
  · simp only [Listing8CopyImage.nodeParams,Listing8ModeOffsets.nodeEntry,Listing8CopyImage.patchLayout,copied.2.1]
    cases mode <;> rfl
  · simp only [Listing8CopyImage.transitionParams,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.nodeEntry,
      Listing8CopyImage.patchLayout,copied.2.1]
    cases mode <;> simp [layout,nodeSpan,pointerSpan,ReaderImage.totalSize,Nat.add_assoc]

theorem word_positions (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (Listing8PointerCopies.word mode (layout mode origin g node rule)).start=main mode origin+(if mode=.x86 then 299 else 421) ∧
    (Listing8PointerCopies.word mode (layout mode origin g node rule)).source=main mode origin+(if mode=.x86 then 247 else 356) ∧
    (Listing8PointerCopies.word mode (layout mode origin g node rule)).destination=main mode origin+(if mode=.x86 then 77 else 133) := by
  have copied:=copy_positions mode origin g node rule
  have second:=(Listing8Initializer.code_geometry mode (layout mode origin g node rule)).1
  simp only [Listing8PointerCopies.word,copied.2.2,copied.2.1,second,pointerField,StringCodec.sourceField]
  cases mode <;> simp [layout,ReaderImage.labelOffset,StringCodec.fieldOffset,Nat.add_assoc]

end SmcTuring.Appendix.Listing8PackedBodyLayout
