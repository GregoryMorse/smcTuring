module
public import SmcTuring.Appendix.Listing8FailureStoreRegions
public import SmcTuring.Appendix.Listing8GlobalControlRegions
public import SmcTuring.Appendix.Listing8FailureTemplateBindings

public section
namespace SmcTuring.Appendix.Listing8GlobalFailureRegions
open Native Listing8FailureLayout

structure Geometry (mode : Mode) (origin : Nat) (l : Layout) : Prop where
  bodyStart : Listing4EntryLayout.mainPC mode origin≤l.start
  bodyEnd : endPC mode l=Listing8JumpLayout.jumpPC mode origin
  callAt : callPC mode l=Listing8JumpLayout.callPC mode origin
  cursorLower : Listing4EntryLayout.mainPC mode origin≤l.cursor
  sentinelLater : Listing8FullTableImage.start mode origin≤l.sentinel

theorem fields (mode : Mode) (origin : Nat) (l : Layout) (geometry : Geometry mode origin l)
    (bounds : Listing8FailureBounds.Bounds mode l) (address count : Nat)
    (allowed : Listing8FailureStoreRegions.Allowed mode l address count) :
    Listing8GlobalControlLayout.Allowed mode origin address count := by
  have positions:=Listing8FailureLayout.positions mode l
  have bodyStart:=geometry.bodyStart
  have bodyEnd:=geometry.bodyEnd
  have cursorBefore:=bounds.cursorBefore
  simp only [Listing8FailureStoreRegions.Allowed,Listing8FailureStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · right;left;constructor
    · exact geometry.cursorLower
    · cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at positions <;> omega
  · right;left
    cases mode <;> simp only [source,StringInit.field,StringCodec.fieldOffset,ownerPC,Mode.wordBytes,
      reduceCtorEq,ite_true,ite_false] at positions ⊢ <;> constructor <;> omega
  · right;left
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at positions <;> constructor <;> omega
  · right;left
    cases mode <;> simp only [andPC,storePC,notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,List.length_cons,List.length_nil]
    all_goals constructor <;> simp only [reduceCtorEq,ite_true,ite_false] at positions <;> omega
  · right;right;left;rw [geometry.callAt];constructor <;> omega
  · right;right;right;exact geometry.sentinelLater

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (geometry : Geometry mode origin l)
    (bounds : Listing8FailureBounds.Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8FailureReuseImage.Current mode l state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8FailureTrace.program mode l state).map StringStack.Form.previous) state :=
  BoundedStoreRegions.monotone mode _ _ _ state (fields mode origin l geometry bounds)
    (Listing8FailureStoreRegions.regions mode l bounds state entry current)

theorem graph_geometry (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Listing8SourceGraph.Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Geometry mode origin (Listing8FailureGeometry.region mode l (Listing8SourceGraph.nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) := by
  have positions:=Listing8FailureGeometry.positions mode l t _ _ ctx.body
  have cursor:=congrArg Listing8ResetLayout.Layout.transitionCursor
    (Listing8GraphReset.actual_region mode origin l t (Listing8SourceGraph.nodePC mode origin g g.halt) [] ctx.boot ctx.body)
  change (Listing8FailureGeometry.region mode l (Listing8SourceGraph.nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).cursor=
    origin+(if mode=.x86 then 129 else 230) at cursor
  refine ⟨?_,Listing8JumpImage.end_position mode origin l t _ ctx.boot ctx.body,
    Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body,?_,?_⟩
  · rw [positions.1,ctx.boot.packed]
    cases mode <;> simp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size]
  · rw [cursor]
    cases mode <;> simp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size]
  · have lower:=Listing8GraphLayout.transition_lower mode origin g.transitions
    have table:=Listing8GraphLayout.table_before_input mode origin g.transitions
    have nodeAfter:=Listing8GraphLayout.node_lower mode origin g.transitions g.halt.val
    change _≤Listing8SourceGraph.nodePC mode origin g g.halt at nodeAfter
    change Listing8FullTableImage.start mode origin≤Listing8GraphLayout.reset mode origin g.transitions at lower
    exact lower.trans (table.trans nodeAfter)

end SmcTuring.Appendix.Listing8GlobalFailureRegions
