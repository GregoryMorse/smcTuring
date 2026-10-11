module
public import SmcTuring.Appendix.Listing8LoopControlReentryFields
public import SmcTuring.Appendix.Listing8LoopControlCases
public import SmcTuring.Appendix.Listing8LoopGraphContext
public import SmcTuring.Appendix.Listing8MainGraphTable

public section
namespace SmcTuring.Appendix.Listing8LoopReentry
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem main_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state)
    (target : Fin g.transitions) (selected : Listing8GraphStep.nextRule g node rule=some target) :
    Listing8MainGraphImage.Current mode origin (nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopControlReentryFields.old mode origin g node rule) (Listing8LoopControl.finish mode origin l t g node rule state) := by
  have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
    intro halted
    have none:=(Listing8GraphStep.halted_iff g node rule).mpr halted
    rw [selected] at none
    cases none
  have registers:=Listing8LoopControl.registers mode origin l t g node rule ctx oldInput state image
  have source:=Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx oldInput state image
  refine ⟨?_,registers.2.2.2.1,Listing8LoopControlMacros.node_current mode origin l t g node rule ctx oldInput state image target,
    Listing8LoopControlMacros.rule_current mode origin l t g node rule ctx oldInput state image target selected,
    Listing8LoopControlReentryFields.patches_current mode origin l t g node rule ctx oldInput state image,Listing8LoopControlReentryFields.helpers_current mode origin l t g node rule ctx oldInput state image,?_,source.1,
    Listing8MainGraphTable.updated_table_current mode origin g node rule _ source.2⟩
  · rw [Listing8LoopControlCases.nonhalt_effect mode origin l t g node rule ctx oldInput state image nonhalt]
    rfl
  · change Listing8InputMask.Intact mode {l.input with head:=nodePC mode origin g (Listing8GraphStep.nextNode g node rule)}
      (Listing8LoopControlReentryFields.old mode origin g node rule).rule (Listing8LoopControlReentryFields.old mode origin g node rule).tape (Listing8LoopControlReentryFields.old mode origin g node rule).pending (Listing8LoopControlReentryFields.old mode origin g node rule).fresh (Listing8LoopControlReentryFields.old mode origin g node rule).mask _
    rw [Listing8InputMask.Intact,Listing8InputReuseFields.head_bytes]
    exact Listing8LoopControlReentryFields.input_current mode origin l t g node rule ctx oldInput state image

/-- Every field of the next complete present main-entry contract follows
from the executed body/CALL/return. No future image is supplied. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state)
    (target : Fin g.transitions) (selected : Listing8GraphStep.nextRule g node rule=some target) :
    Listing8LoopControl.Current mode origin (nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopControlReentryFields.old mode origin g node rule) (Listing8LoopControl.finish mode origin l t g node rule state) := by
  have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
    intro halted
    have none:=(Listing8GraphStep.halted_iff g node rule).mpr halted
    rw [selected] at none
    cases none
  refine ⟨⟨⟨⟨main_current mode origin l t g node rule ctx oldInput state image target selected,Listing8LoopControlFrames.direction_fragments mode origin l t g node rule ctx oldInput state image⟩,
    Listing8LoopControlFrames.state_fragments mode origin l t g node rule ctx oldInput state image⟩,Listing8LoopControlFrames.failure_fragments mode origin l t g node rule ctx oldInput state image⟩,
    Listing8LoopControlFrames.entry_packet mode origin l t g node rule ctx oldInput state image,Listing8LoopControlFrames.prefix_packet mode origin l t g node rule ctx oldInput state image,?_,
    Listing8LoopControlFrames.fail_packet mode origin l t g node rule ctx oldInput state image⟩
  have packet:=Listing8LoopControlFrames.call_packet mode origin l t g node rule ctx oldInput state image
  rw [Listing8LoopControlCases.nonfailure mode origin l t g node rule ctx oldInput state image nonhalt] at packet
  exact packet

theorem exists_next (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state)
    (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    ∃ target : Fin g.transitions,Listing8GraphStep.nextRule g node rule=some target ∧
      Context mode origin (nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target ∧
      Listing8LoopControl.Current mode origin (nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule)
        (Listing8GraphStep.nextNode g node rule) target (Listing8LoopControlReentryFields.old mode origin g node rule) (Listing8LoopControl.finish mode origin l t g node rule state) := by
  obtain ⟨target,selected⟩:=Listing8GraphLabels.nonhalt_rule g node rule nonhalt
  exact ⟨target,selected,Listing8LoopGraphContext.next mode origin l t g node rule target ctx,current mode origin l t g node rule ctx oldInput state image target selected⟩

end SmcTuring.Appendix.Listing8LoopReentry
