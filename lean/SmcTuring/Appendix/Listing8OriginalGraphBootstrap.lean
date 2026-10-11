module
public import SmcTuring.Appendix.Listing8JointOriginalGraphMain
public import SmcTuring.Appendix.Listing8LoopOriginalImage

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphBootstrap
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

theorem nodes_initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) (memory : ByteMemory.Memory) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g) (initialMemory mode origin l t g node rule memory) := by
  apply Listing8LiveNodePacket.initial_from_packets
  intro index item found
  have within : index<g.nodes := by
    have small:=(List.getElem?_eq_some_iff.mp found).1
    rw [Listing8GraphNodeImage.length] at small;exact small
  let query : Fin g.nodes:=⟨index,within⟩
  have actual:=Listing8GraphNodeImage.lookup mode origin g query
  rw [found] at actual
  have same:=Option.some.inj actual
  subst item
  change ByteMemory.bytesAt _ (nodePC mode origin g query) (Listing8Prototypes.nodeSpan mode)=
    Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin g query)
  by_cases chosen : query=node
  · rw [chosen];exact Listing8GraphInputInitial.source_current mode origin l t g node rule ctx memory
  · exact Listing8GraphInputInitial.other_current mode origin l t g node rule ctx memory query chosen

theorem rules_initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) (memory : ByteMemory.Memory) :
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (initialMemory mode origin l t g node rule memory) := by
  have after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin))+5≤Listing8FullTableImage.start mode origin := by
    change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt))+5≤_
    rw [Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body]
    have ordered:=Listing8GlobalControlLayout.ordered mode origin
    omega
  have endNode : Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)≤l.sourceNode := by
    simp only [Listing8TransitionTable.endPC,table_length]
    rw [ctx.nodeLocated]
    exact (Listing8GraphLayout.table_before_input mode origin g.transitions).trans (Listing8GraphLayout.node_lower mode origin g.transitions node.val)
  exact Listing8TableImage.current mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) (Listing8FullTableImage.start mode origin) (table mode origin g) rule.val
    (selected mode origin g node rule) ctx.ruleLocated ctx.resources ctx.body _ after (Or.inr endNode)
    (Listing8FullTableImage.extra_current mode origin (table mode origin g)
      (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g)
        (Listing8GraphNodeImage.image mode origin g memory)))

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory := by
  rw [Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed]
  exact Listing8OriginalGraphCatalog.from_initial mode origin g _ (nodes_initial mode origin l t g node rule ctx memory)
    (rules_initial mode origin l t g node rule ctx memory)

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
      (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have bounds:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have positions:=coordinates mode l
  have starts:=endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  change l.start≤secondStart mode l at starts
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  exact BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) _ _ _
    (fun address count slots => by
      have early:=Listing8ControlStoreFields.slot_bound mode origin l t g node rule ctx address count slots
      omega)
    (Listing4EntrySlotRegions.entry mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (after : Listing8FullTableImage.start mode origin≤observed) :
    ByteMemory.bytesAt (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory observed count=
      ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) observed count := by
  have kept:=StringStoreTemplateRuns.preserve mode (fun address width => address+width≤Listing8FullTableImage.start mode origin)
    (fun reached => ByteMemory.bytesAt reached observed count=ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) observed count)
    _ (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (by rw [Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed])
    (fun before address packet same early => by
      rw [ByteMemory.bytes_at_frame before address packet observed count (by
        intro index;unfold ByteMemory.Inside;have small:=index.isLt;omega)]
      exact same) (regions mode origin l t g node rule ctx memory seed)
  have ending:=StringTemplateStates.at_prefix mode _ _ [] (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (by simpa only [List.append_nil] using kept)
  rw [Listing8GraphEntryWrites.boot_run mode origin l t g node rule ctx memory seed] at ending
  exact ending

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) reached.principal.memory)
      (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have stores:=regions mode origin l t g node rule ctx memory seed
  have global:=Listing8GlobalControlTemplates.initial mode origin _ (Listing8GlobalInitialControl.current mode origin l t g node rule ctx memory seed)
  have globalRegions:=BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) (Listing8GlobalControlLayout.Allowed mode origin)
    _ _ (fun _ _ slots => Or.inl slots)
    (Listing4EntrySlotRegions.entry mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  exact JointTemplateStates.join mode _ _ _ _ (Listing8GlobalControlTemplates.all_decodes mode origin _ _ global globalRegions)
    (StringStoreTemplateRuns.preserve mode _ _ _ _ (initial mode origin l t g node rule ctx memory seed)
      (Listing8OriginalGraphFailureRun.store mode origin g) stores)

end SmcTuring.Appendix.Listing8OriginalGraphBootstrap
