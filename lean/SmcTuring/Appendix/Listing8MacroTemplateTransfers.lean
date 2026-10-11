module
public import SmcTuring.Native.StringEncodedTemplates
public import SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes

public section
namespace SmcTuring.Appendix.Listing8MacroTemplateTransfers
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets

@[expose] def Certificate (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode) : Prop :=
  StringPacketRegions.Run mode p
    ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state ∧
  StringTemplateStates.Run mode (fun current => StringMacroTemplates.Intact mode p current.principal.memory)
    ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state ∧
  StringTemplateStates.Run mode (fun current => StringEncodedTemplates.Decodes mode p current.principal.memory)
    ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state

theorem constructed (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode p state) : Certificate mode p state :=
  ⟨StringMacroTemplateWrites.complete mode p state ready,StringMacroTemplateWrites.templates mode p state ready,
    StringEncodedTemplates.all_states mode p state ready⟩

theorem at_prefix (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (certificate : Certificate mode p state) (before after : List (StringStack.Form mode))
    (cut : (StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)=before++after) :
    StringMacroTemplates.Intact mode p (StringWrites.run mode before state).principal.memory ∧
    StringEncodedTemplates.Decodes mode p (StringWrites.run mode before state).principal.memory := by
  rcases certificate with ⟨_,intact,decoded⟩
  rw [cut] at intact decoded
  exact ⟨StringTemplateStates.at_prefix mode _ before after state intact,
    StringTemplateStates.at_prefix mode _ before after state decoded⟩

@[expose] def Both (mode : Mode) (l : Layout) (state : StringExecution.State mode) : Prop :=
  Certificate mode (nodeParams mode l) state ∧
  Certificate mode (transitionParams mode l) (Listing8CopyTrace.first mode l state)

/-- The second macro's entry and current bytes come from the first complete
actual execution. No later image, packet, readiness or trace is supplied. -/
theorem pair (mode : Mode) (l : Layout) (r : Resources mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (forward : state.backwards=false)
    (nodeMacro : ByteMemory.bytesAt state.principal.memory l.start
      (StringMacroLayout.bytes mode (nodeParams mode l)).length=StringMacroLayout.bytes mode (nodeParams mode l))
    (ruleMacro : ByteMemory.bytesAt state.principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l)) :
    Both mode l state := by
  have first := Listing8LiveCopies.first_ready mode l r state entry forward nodeMacro
  have second := Listing8LiveCopies.second_ready mode l r state first ruleMacro
  exact ⟨constructed mode _ state first,constructed mode _ _ second⟩

theorem live (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    Both mode l state :=
  pair mode l r state entry forward (Listing8MainCopyImage.node_current mode l v _ current)
    (Listing8MainCopyImage.rule_current mode l v _ current)

theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Both mode l (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have current := Listing8GraphCopyOwnerPrefixes.original_current mode origin l t g node rule ctx memory seed
  apply live mode l _ ctx.resources _ _ _ current
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl

/-- A selected actual CALL/backedge provides the next macro/source operands
and static resources. Certificates cover both complete next macro executions. -/
theorem next_pair (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Both mode (Listing8GraphMacroImages.nextLayout mode origin l g node rule target)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) := by
  have registers := Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  exact pair mode _ (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)
    _ registers.1 registers.2.2.2.2.1
    (Listing8GraphMacroImages.node_current mode origin l t g node rule target ctx memory seed)
    (Listing8GraphMacroImages.rule_current mode origin l t g node rule target ctx selected memory seed)

end SmcTuring.Appendix.Listing8MacroTemplateTransfers
