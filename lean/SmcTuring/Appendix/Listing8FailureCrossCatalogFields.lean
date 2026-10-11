module
public import SmcTuring.Appendix.Listing8SentinelCatalogTransport
public import SmcTuring.Appendix.Listing8StateStoreFields

public section
namespace SmcTuring.Appendix.Listing8FailureCrossCatalogFields
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def region (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) :=
  Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
@[expose] def Allowed (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (address count : Nat) : Prop :=
  Listing8MainCatalogTransport.Allowed mode origin l address count ∨
    (address=nodePC mode origin g g.halt ∧ count≤mode.wordBytes)

theorem fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8FailureStoreRegions.Allowed mode (region mode origin l g) address count) :
    Allowed mode origin l g address count := by
  let r:=region mode origin l g
  have geometry:=Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  have stateBound:=Listing8StateStoreFields.inside mode origin l t g node rule ctx
  have stateEnd:=(Listing8StateLayout.positions mode (Listing8StateGeometry.region mode l)).2.2.2
  have startBound : codeEnd mode l≤r.start := by
    change codeEnd mode l≤Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l)
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at stateEnd <;> omega
  have callBound : Listing8FailureLayout.callPC mode r+5≤Listing8FullTableImage.start mode origin := by
    have callAt : Listing8FailureLayout.callPC mode r=Listing8JumpLayout.callPC mode origin := geometry.callAt
    rw [callAt];omega
  change (address,count)∈Listing8FailureStoreRegions.fields mode r at allowed
  simp only [Listing8FailureStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with h | h | h | h | h | h <;> cases h
  · left;right;right;right
    exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  · left;right;left
    cases mode <;> simp only [Listing8FailureLayout.source,StringInit.field,StringCodec.fieldOffset,
      Listing8FailureLayout.ownerPC,Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.xorPC,
      Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,Listing8FailureLayout.notPC,Listing8FailureLayout.comparisonPC,
      StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Listing8FailureLayout.stackSpan,Mode.wordBytes,
      reduceCtorEq,ite_true,ite_false] at callBound ⊢ <;> omega
  · left;right;left
    cases mode <;> simp only [Listing8FailureLayout.mask,Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,
      Listing8FailureLayout.xorPC,Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,Listing8FailureLayout.notPC,
      Listing8FailureLayout.comparisonPC,Listing8FailureLayout.ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,
      wordPrefix,Listing8FailureLayout.stackSpan,reduceCtorEq,ite_true,ite_false] at callBound ⊢ <;> omega
  · left;right;left
    cases mode <;> simp only [Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.xorPC,
      Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,Listing8FailureLayout.notPC,Listing8FailureLayout.comparisonPC,
      Listing8FailureLayout.ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Listing8FailureLayout.stackSpan,
      reduceCtorEq,ite_true,ite_false] at callBound ⊢ <;> omega
  · left;right;left
    have source:=(Listing8FailureLayout.positions mode r).2.2.2.2
    have before:=(Listing8FailureLayout.positions mode r).2.2.2.1
    refine ⟨?_,by omega⟩
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at source <;> omega
  · right
    exact ⟨rfl,Nat.le_refl _⟩

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (region mode origin l g).start)
    (current : Listing8FailureReuseImage.Current mode (region mode origin l g) state.principal.memory) :
    StringStoreRegions.Run mode (Allowed mode origin l g)
      ((Listing8FailureTrace.program mode (region mode origin l g) state).map StringStack.Form.previous) state :=
  BoundedStoreRegions.monotone mode _ _ _ state (fields mode origin l t g node rule ctx)
    (Listing8FailureStoreRegions.regions mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) state entry current)

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) memory)
    (allowed : Allowed mode origin l g address packet.length) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) (ByteMemory.putBytes memory address packet) := by
  rcases allowed with main | ⟨rfl,small⟩
  · exact Listing8MainCatalogTransport.store mode origin l t g node rule ctx memory address packet initial main
  · exact Listing8SentinelCatalogTransport.store mode origin l t g node rule ctx memory packet initial small

end SmcTuring.Appendix.Listing8FailureCrossCatalogFields
