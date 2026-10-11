module
public import SmcTuring.Appendix.Listing8GlobalMainPrefixRegions
public import SmcTuring.Appendix.Listing8GraphPointerWrites
public import SmcTuring.Native.StringStackTraceDeterminism
public import SmcTuring.Native.StringTracePrefixes

public section
namespace SmcTuring.Appendix.Listing8GlobalOriginalPrefix
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringStoreRegions.Run
abbrev Targets:=Listing8PointerCopies.Targets

theorem copying (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8MainCopyImage.Current mode l (values mode origin g node rule)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory := by
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  change Listing8MainCopyImage.Current mode l (values mode origin g node rule)
    (image mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory))
  apply Listing8MainCopyImage.from_packets
  · exact initial_node_macro mode l _ ctx.resources _
  · exact initial_transition_macro mode l _ ctx.resources _
  · exact initial_patches mode l _ ctx.resources _
  · simpa only [sourceNodeBytes,node_length] using initial_source_node mode l (values mode origin g node rule) ctx.resources
      (Listing8GraphCopyWrites.copyBacking mode origin l t g memory)
  · simpa only [sourceTransitionBytes,transition_length] using initial_source_transition mode l (values mode origin g node rule)
      (Listing8GraphCopyWrites.copyBacking mode origin l t g memory)

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8MainPrefix.Current mode l t (values mode origin g node rule)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory := by
  refine ⟨copying mode origin l t g node rule ctx memory seed,?_⟩
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  exact Listing8PointerImage.initial_helper mode l t _ ctx.resources ctx.body.state.head.input.joined
    (Listing8GraphPointerWrites.helperBacking mode origin l g memory)

/-- The original bootstrap's actual result supplies every present copy,
retarget, owner and helper packet needed by the generic main prefix. -/
theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have entry : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode l.start := by rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  have forward : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).backwards=false := by
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  exact Listing8GlobalMainPrefixRegions.regions mode origin l t g node rule ctx _ entry forward
    (current mode origin l t g node rule ctx memory seed)

/-- Determinism binds the globally safe generic prefix stores to the original
emitted first-pass form list and its actual reached state. No equality or
future packet is a premise of this original-image wrapper. -/
theorem forms_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8GraphPointerWrites.forms mode l t (values mode origin g node rule))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have entry : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode l.start := by rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  have forward : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).backwards=false := by
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  have generic:=StringDwordWritesBridge.trace mode (Listing8MainPrefix.trace mode l t _
    (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds _ entry forward
    (current mode origin l t g node rule ctx memory seed))
  have boot:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have original:=StringTracePrefixes.tail mode (Listing4EntryLayout.forms mode origin)
    (Listing8GraphPointerWrites.forms mode l t (values mode origin g node rule)) _ _ _
    (Listing8GraphPointerWrites.execute mode origin l t g node rule ctx memory seed).1 boot
  have oldSize:=Listing8GraphPointerWrites.instruction_count mode origin l t g node rule
  rw [Listing8GraphPointerWrites.program,List.length_append,Listing4EntryLayout.instruction_count] at oldSize
  have sizes : ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)).length=
      (Listing8GraphPointerWrites.forms mode l t (values mode origin g node rule)).length := by
    rw [List.length_map,Listing8MainPrefix.instruction_count]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at oldSize ⊢ <;> omega
  exact (StringStackTraceDeterminism.equal_length mode _ _ _ _ _ sizes generic original).1 ▸
    regions mode origin l t g node rule ctx memory seed

end SmcTuring.Appendix.Listing8GlobalOriginalPrefix
