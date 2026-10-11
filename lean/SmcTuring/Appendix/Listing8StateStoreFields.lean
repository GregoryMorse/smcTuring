module
public import SmcTuring.Appendix.Listing8MainCatalogTransport

public section
namespace SmcTuring.Appendix.Listing8StateStoreFields
open Native Listing8CopyImage Listing8SourceGraph Listing8StateLayout Listing8StateBounds
abbrev Targets:=Listing8PointerCopies.Targets

theorem inside (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    codeEnd mode l≤(Listing8StateGeometry.region mode l).start ∧
      endPC mode (Listing8StateGeometry.region mode l)≤Listing8FullTableImage.start mode origin := by
  have direction:=Listing8HeadStoreFields.inside mode origin l t g node rule ctx
  have coordinates:=Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)
  have ending:=coordinates.2.2.2.2.2.2.2
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  have state:=(Listing8GlobalMainBounds.state mode origin l t g node rule ctx).2
  constructor
  · change codeEnd mode l≤Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at ending <;> omega
  · omega

theorem helper_fields (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ helper∈helpers mode (Listing8StateGeometry.region mode l),
      Listing8MainCatalogTransport.Allowed mode origin l helper.source 4 ∧
      Listing8MainCatalogTransport.Allowed mode origin l helper.destination 4 := by
  have bounds:=inside mode origin l t g node rule ctx
  intro helper member
  cases mode
  all_goals simp only [helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp only [Listing8MainCatalogTransport.Allowed,Listing8StateGeometry.region,endPC,updatePC,maskPC,newPC,
    halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at bounds ⊢
  all_goals omega

theorem packet_fields (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ site∈packets mode (Listing8StateGeometry.region mode l),Listing8MainCatalogTransport.Allowed mode origin l site.target 4 := by
  have bounds:=inside mode origin l t g node rule ctx
  intro site member
  cases mode
  all_goals simp only [packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Listing8MainCatalogTransport.Allowed,Listing8StateGeometry.region,endPC,updatePC,maskPC,newPC,
    halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at bounds ⊢
  all_goals omega

theorem regions (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8StateGeometry.region mode l).start) :
    StringStoreRegions.Run mode (Listing8MainCatalogTransport.Allowed mode origin l)
      ((Listing8StateTrace.program mode (Listing8StateGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)) state := by
  let layout:=Listing8StateGeometry.region mode l
  have bounds:=Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state
  have first:=CopyStoreRegions.sequence mode _ (helpers mode layout) layout.start (helper_chain mode layout)
    (helper_valid mode layout bounds) (helper_fields mode origin l t g node rule ctx) state entry
  have last:=DwordXorRegionRuns.packets mode _ (packets mode layout) (newPC mode layout) (packet_chain mode layout)
    (packet_valid mode layout bounds) (packet_fields mode origin l t g node rule ctx)
    (Listing8StateTrace.helperFinish mode layout state) (Listing8StateTrace.helper_endpoint mode layout bounds state entry)
  rw [Listing8StateTrace.program,List.map_append,StringStoreRegions.append,StringDwordRuns.run]
  exact ⟨first,last⟩

end SmcTuring.Appendix.Listing8StateStoreFields
