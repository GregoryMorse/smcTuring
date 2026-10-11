module
public import SmcTuring.Appendix.Listing8InputCrossCatalogFields
public import SmcTuring.Appendix.Listing8GlobalSelectionRegions
public import SmcTuring.Appendix.Listing8WholeHeadTemplates

public section
namespace SmcTuring.Appendix.Listing8HeadStoreFields
open Native Listing8CopyImage Listing8SourceGraph Listing8DirectionLayout Listing8HeadTailBounds
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def Allowed (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (address count : Nat) : Prop :=
  (codeEnd mode l≤address ∧ address+count≤Listing8JumpLayout.jumpPC mode origin) ∨
    (StringCodec.sourceField mode l.start≤address ∧ address+count≤StringCodec.sourceField mode l.start+mode.wordBytes)

theorem inside (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    codeEnd mode l≤(Listing8DirectionGeometry.region mode l).start ∧
      endPC mode (Listing8DirectionGeometry.region mode l)≤Listing8JumpLayout.jumpPC mode origin := by
  have pos:=Listing8LiteralInput.positions mode l.input
  have copies:=(Listing8PointerCopies.sizes mode l t).2.1
  have joined:=ctx.body.state.head.input.joined
  refine ⟨?_,(Listing8GlobalMainBounds.direction mode origin l t g node rule ctx).2⟩
  change codeEnd mode l≤Listing8LiteralInput.endPC mode l.input
  have ending:=pos.2.2.2.2.2.2.2
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at ending <;> omega

theorem direction (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8DirectionGeometry.region mode l).start) :
    StringStoreRegions.Run mode (Allowed mode origin l)
      ((Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)) state :=
  BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ lower upper => Or.inl ⟨lower,upper⟩)
    (Listing8DirectionWrites.owned mode (codeEnd mode l) (Listing8JumpLayout.jumpPC mode origin) _
      (inside mode origin l t g node rule ctx) ctx.body.state.head.capacity state entry)

theorem xor_fields (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ helper∈xorLayouts mode (Listing8DirectionGeometry.region mode l),
      Allowed mode origin l helper.source 4 ∧ Allowed mode origin l helper.destination 4 := by
  have bounds:=inside mode origin l t g node rule ctx
  have cursor:=ctx.body.state.head.input.fields.cursorLabel
  intro helper member
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp only [Allowed,Listing8DirectionGeometry.region,endPC,directionPC,maskPC,selectionEnd,combinedPC,
    forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,
    DwordLayout.storeSize,Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at bounds ⊢
  all_goals try rw [cursor]
  all_goals omega

theorem packet_fields (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ site∈masks mode (Listing8DirectionGeometry.region mode l)++heads mode (Listing8DirectionGeometry.region mode l),
      Allowed mode origin l site.target 4 := by
  have bounds:=inside mode origin l t g node rule ctx
  have cursor:=ctx.body.state.head.input.fields.cursorLabel
  intro site member
  cases mode
  all_goals simp only [masks,heads,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp only [Allowed,Listing8DirectionGeometry.region,endPC,directionPC,maskPC,selectionEnd,combinedPC,
    forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,
    DwordLayout.storeSize,Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at bounds ⊢
  all_goals try rw [cursor]
  all_goals omega

theorem head (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (selectionEnd mode (Listing8DirectionGeometry.region mode l))) :
    StringStoreRegions.Run mode (Allowed mode origin l)
      ((Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)) state := by
  let layout:=Listing8DirectionGeometry.region mode l
  have bounds:=Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head
  have first:=DwordXorRegionRuns.sequence mode _ (xorLayouts mode layout) (selectionEnd mode layout) (xor_chain mode layout)
    (xor_valid mode layout bounds) (xor_fields mode origin l t g node rule ctx) state entry
  have fields:=packet_fields mode origin l t g node rule ctx
  have middle:=DwordXorRegionRuns.packets mode _ (masks mode layout) (maskPC mode layout) (masks_chain mode layout)
    (fun site member => packets_valid mode layout bounds site (List.mem_append_left _ member))
    (fun site member => fields site (List.mem_append_left _ member))
    (Listing8HeadTailTrace.xorFinish mode layout state) (Listing8HeadTailTrace.xor_endpoint mode layout bounds state entry)
  have last:=DwordXorRegionRuns.packets mode _ (heads mode layout) (directionPC mode layout) (heads_chain mode layout)
    (fun site member => packets_valid mode layout bounds site (List.mem_append_right _ member))
    (fun site member => fields site (List.mem_append_right _ member))
    (Listing8HeadTailTrace.maskFinish mode layout state) (Listing8HeadTailTrace.mask_endpoint mode layout bounds state entry)
  rw [Listing8HeadTailTrace.program,List.map_append,List.map_append,StringStoreRegions.append,
    StringStoreRegions.append,StringWrites.run_append,DwordXorWrites.sequence_run]
  unfold Listing8HeadTailTrace.xorFinish
  rw [DwordPacketWrites.run]
  simpa only [Listing8HeadTailTrace.maskFinish,Listing8HeadTailTrace.xorFinish] using And.intro (And.intro first middle) last

theorem complete (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8DirectionGeometry.region mode l).start) :
    StringStoreRegions.Run mode (Allowed mode origin l)
      ((Listing8WholeHeadTemplates.program mode (Listing8DirectionGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)) state := by
  rw [Listing8WholeHeadTemplates.program,List.map_append,StringStoreRegions.append]
  have run : StringWrites.run mode ((Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)) state=
      Listing8DirectionTrace.finish mode (Listing8DirectionGeometry.region mode l) state := by
    rw [Listing8DirectionTrace.program,List.map_append,StringWrites.run_append,StringDwordRuns.run]
    unfold Listing8DirectionTrace.helperFinish
    rw [DwordPacketWrites.run];rfl
  rw [run]
  exact ⟨direction mode origin l t g node rule ctx state entry,
    head mode origin l t g node rule ctx _ (Listing8DirectionTrace.endpoint mode _ ctx.body.state.head.capacity state entry)⟩

end SmcTuring.Appendix.Listing8HeadStoreFields
