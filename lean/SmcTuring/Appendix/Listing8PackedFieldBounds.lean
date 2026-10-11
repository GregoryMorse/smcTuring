module
public import SmcTuring.Appendix.Listing8PackedPointerBounds

public section
namespace SmcTuring.Appendix.Listing8PackedFieldBounds
open Native Listing8SourceGraph Listing8Prototypes Listing8CopyImage Listing8PackedBodyLayout Listing8PackedResources

theorem masks (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8LiteralInput.distributionLayouts mode (layout mode origin g node rule).input=
      match mode with
      | .x86 => [⟨main mode origin+433,main mode origin+483,main mode origin+630⟩,
          ⟨main mode origin+450,main mode origin+483,main mode origin+583⟩]
      | .x64 => [⟨main mode origin+617,main mode origin+705,main mode origin+994⟩,
          ⟨main mode origin+635,main mode origin+705,main mode origin+1004⟩,
          ⟨main mode origin+653,main mode origin+705,main mode origin+898⟩,
          ⟨main mode origin+671,main mode origin+705,main mode origin+908⟩] := by
  cases mode <;> simp [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts,
    Listing8LiteralInput.distributionStart,Listing8LiteralInput.ownerPC,Listing8LiteralInput.copyStart,
    Listing8LiteralInput.maskField,Listing8LiteralInput.updateStart,Listing8LiteralInput.gap,layout,input,
    DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem input_fields (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8InputBounds.Fields mode (layout mode origin g node rule) := by
  have body:=body_capacity mode origin g node bounds
  have before:=before_table mode origin
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  refine ⟨rfl,rfl,?_,?_,?_,?_⟩
  · intro helper member
    rw [masks] at member
    rw [input_end]
    cases mode
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals simp
  · intro helper member
    rw [masks] at member
    cases mode
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals (simp [Mode.wordBytes] at body ⊢;omega)
  · intro helper member long
    subst mode
    rw [masks] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp [DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.storeSize,Relocation.SignedDelta,Relocation.delta];omega
  · intro helper member
    rw [masks] at member
    change helper.destination+4≤nodePC mode origin g node+6 ∨ nodePC mode origin g node+10≤helper.destination
    cases mode
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals simp only [reduceCtorEq,ite_true,ite_false] at before
    all_goals apply Or.inl
    all_goals dsimp
    all_goals omega

theorem graph_fields (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8GraphOwnerBounds.Fields mode (layout mode origin g node rule) := by
  have body:=body_capacity mode origin g node bounds
  have before:=before_table mode origin
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin rule.val
  change Listing8FullTableImage.start mode origin≤rulePC mode origin g rule at ruleAfter
  have copied:=copy_positions mode origin g node rule
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [input_end]
    cases mode <;> simp [layout]
  · cases mode <;> simp [layout,Mode.wordBytes] at body ⊢ <;> omega
  · apply Or.inr
    cases mode <;> simp [layout] <;> simp only [reduceCtorEq,ite_true,ite_false] at before <;> omega
  · apply Or.inr
    cases mode <;> simp [layout] <;> simp only [reduceCtorEq,ite_true,ite_false] at before <;> omega
  · intro long;subst mode
    rw [copied.1]
    simp [layout,input,Listing8LiteralInput.sourceField,Listing8LiteralInput.ownerPC,Listing8LiteralInput.copyStart,
      DwordLayout.span,DwordLayout.storeSize,Relocation.SignedDelta,Relocation.delta];omega
  · intro long;subst mode
    rw [copied.2.1]
    simp [layout,input,currentEntry,pointerSpan,ReaderImage.totalSize,Listing8LiteralInput.scalarField,
      Listing8LiteralInput.ownerPC,Listing8LiteralInput.copyStart,DwordLayout.span,DwordLayout.storeSize,
      Relocation.SignedDelta,Relocation.delta];omega
  · intro long;subst mode
    rw [copied.2.1]
    simp [layout,input,newEntry,currentEntry,pointerSpan,ReaderImage.totalSize,Listing8LiteralInput.updateStart,
      Listing8LiteralInput.distributionStart,Listing8LiteralInput.ownerPC,Listing8LiteralInput.copyStart,Listing8LiteralInput.gap,
      DwordLayout.span,DwordLayout.storeSize,Relocation.SignedDelta,Relocation.delta];omega
  · intro long;subst mode
    rw [copied.2.1]
    simp [layout,directionEntry,newEntry,currentEntry,pointerSpan,ReaderImage.totalSize,Relocation.SignedDelta,Relocation.delta];omega

end SmcTuring.Appendix.Listing8PackedFieldBounds
