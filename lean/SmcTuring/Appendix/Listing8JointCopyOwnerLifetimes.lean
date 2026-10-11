module
public import SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun

public section
namespace SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes Listing8CopyOwnerPrefixes
open Listing8CopyOwnerLifetimes Listing8OwnerTemplateCollection StringMacroLayout StringMacroEffects
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

@[expose] def macroForms (mode : Mode) (p : Params) :=
  (StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)
@[expose] def restoreForms (mode : Mode) (p : Params) :=
  ((StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size)++
    (StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size)).map
    (StringWrites.liftString mode)
@[expose] def Joint (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph)
    (born : List (Template mode)) (state : StringExecution.State mode) : Prop :=
  Listing8JointLocalMain.Property mode origin l v g state ∧
  ∃ packet : StringWrites.Packet,
    (Listing8CopiedOwnerActiveRun.Allowed mode (Listing8OwnerImage.owners mode l v) packet ∨
      ((packet.address=l.sourceNode ∨ packet.address=l.sourceTransition) ∧ packet.bytes.length=mode.wordBytes) ∨
      packet.address=nodePC mode origin g g.halt ∧ packet.bytes.length=mode.wordBytes) ∧
    (∀ template∈Listing8OriginalGraphCatalog.catalog mode origin g,Outside mode template packet →
      Intact mode template state.principal.memory ∧ Decodes mode template state.principal.memory) ∧
    (∀ template∈born,Outside mode template packet →
      Intact mode template state.principal.memory ∧ Decodes mode template state.principal.memory)

theorem from_all (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph)
    (born : List (Template mode)) (state : StringExecution.State mode)
    (main : Listing8JointLocalMain.Property mode origin l v g state)
    (current : Property mode born state.principal.memory) : Joint mode origin l v g born state := by
  obtain ⟨packet,allowed,originals⟩ := main.1.2
  exact ⟨main,packet,allowed,originals,fun template member _ => ⟨current.1 template member,current.2 template member⟩⟩

theorem property_append (mode : Mode) (first second : List (Template mode)) (memory : ByteMemory.Memory)
    (a : Property mode first memory) (b : Property mode second memory) : Property mode (first++second) memory := by
  constructor
  · intro template member
    rcases List.mem_append.mp member with left | right
    · exact a.1 template left
    · exact b.1 template right
  · intro template member
    rcases List.mem_append.mp member with left | right
    · exact a.2 template left
    · exact b.2 template right

theorem macros (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g)
      (macroForms mode (nodeParams mode l)) state ∧
    StringTemplateStates.Run mode (Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g)
      (macroForms mode (transitionParams mode l)) (Listing8CopyTrace.first mode l state) := by
  have all := Listing8JointLocalMain.maintained mode origin l t g node rule ctx old state current
  rw [Listing8JointOriginalGraphMain.forms_shape,StringTemplateStates.append] at all
  have copies := all.1
  simp only [Listing8MainCopies.program,Listing8CopyTrace.program,List.map_append] at copies
  change StringTemplateStates.Run mode _ (macroForms mode (nodeParams mode l)++macroForms mode (transitionParams mode l)) state at copies
  rw [StringTemplateStates.append,macroForms,StringWrites.run_lift_string,program_run] at copies
  exact copies

theorem restore_slice (mode : Mode) (p : Params) (property : StringExecution.State mode → Prop)
    (state : StringExecution.State mode) (all : StringTemplateStates.Run mode property (macroForms mode p) state) :
    StringTemplateStates.Run mode property (restoreForms mode p) (copied mode p state) := by
  have shape : macroForms mode p=
      ((StringSetup.forms mode p.start p.source p.destination++StringMoves.forms mode (StringPlan.widths mode p.size)).map
        (StringWrites.liftString mode))++restoreForms mode p := by
    simp only [macroForms,restoreForms,StringProgram.forms,List.map_append,List.append_assoc,sourceTail,destinationTail]
  rw [shape,StringTemplateStates.append] at all
  have result := all.2
  rw [StringWrites.run_lift_string,StringExecution.run_append] at result
  exact result

theorem first_restorations (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode
      (Joint mode origin l (values mode origin g node rule) g
        (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)))
      (restoreForms mode (nodeParams mode l)) (copied mode (nodeParams mode l) state) := by
  have graph := current.body.state.head.graph
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have owners := Listing8CopyOwnerLifetimeRun.node_restorations mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying
  have main := restore_slice mode (nodeParams mode l) _ state (macros mode origin l t g node rule ctx old state current).1
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached paired => from_all mode origin l _ g _ reached paired.1 paired.2)
    (JointTemplateStates.join mode _ _ _ _ main owners)

theorem second_macro (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode
      (Joint mode origin l (values mode origin g node rule) g
        (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)))
      (macroForms mode (transitionParams mode l)) (Listing8CopyTrace.first mode l state) := by
  have graph := current.body.state.head.graph
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have owners := Listing8CopyOwnerLifetimeRun.node_second_macro mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached paired => from_all mode origin l _ g _ reached paired.1 paired.2)
    (JointTemplateStates.join mode _ _ _ _ (macros mode origin l t g node rule ctx old state current).2 owners)


theorem moves_cut (mode : Mode) (p : Params) (first rest : List Nat)
    (split : StringPlan.widths mode p.size=first++rest) :
    (StringMoves.forms mode (StringPlan.widths mode p.size)).map (StringWrites.liftString mode)=
      (StringMoves.forms mode first).map (StringWrites.liftString mode)++
      (StringMoves.forms mode rest).map (StringWrites.liftString mode) := by
  simp only [split,StringMoves.forms,List.map_append]

theorem first_moves (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (first rest : List Nat) (split : StringPlan.widths mode (nodeSpan mode)=first++rest) :
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) first.sum)
      (StringMacroCopyPrefixes.reached mode (nodeParams mode l) state first) := by
  have graph := current.body.state.head.graph
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have ready := Listing8LiveCopies.first_ready mode l ctx.resources state graph.entry graph.forward
    (Listing8MainCopyImage.node_current mode l _ _ image.prefixCurrent.copying)
  have main := Listing8JointCopyOwnerPrefixes.macro_prefix mode (nodeParams mode l) _ state _ _
    (moves_cut mode (nodeParams mode l) first rest split) (macros mode origin l t g node rule ctx old state current).1
  rw [StringMacroCopyPrefixes.whole_prefix] at main
  exact from_all mode origin l _ g _ _ main
    (reached_inventory mode (nodeParams mode l) _ state ready (node_current mode l _ _ image.prefixCurrent.copying.node)
      (node_bounded mode l _) first rest split)

theorem second_moves (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (first rest : List Nat) (split : StringPlan.widths mode (transitionSpan mode)=first++rest) :
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)++
        inventory mode (transitionParams mode l) (transitionTemplates mode l (values mode origin g node rule)) first.sum)
      (StringMacroCopyPrefixes.reached mode (transitionParams mode l) (Listing8CopyTrace.first mode l state) first) := by
  have graph := current.body.state.head.graph
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have ready := Listing8LiveCopies.first_ready mode l ctx.resources state graph.entry graph.forward
    (Listing8MainCopyImage.node_current mode l _ _ image.prefixCurrent.copying)
  have next := Listing8LiveCopies.second_ready mode l ctx.resources state ready
    (Listing8MainCopyImage.rule_current mode l _ _ image.prefixCurrent.copying)
  have main := Listing8JointCopyOwnerPrefixes.macro_prefix mode (transitionParams mode l) _ _ _ _
    (moves_cut mode (transitionParams mode l) first rest split) (macros mode origin l t g node rule ctx old state current).2
  have nodes := Listing8JointCopyOwnerPrefixes.macro_prefix mode (transitionParams mode l) _ _ _ _
    (moves_cut mode (transitionParams mode l) first rest split)
    (Listing8CopyOwnerLifetimeRun.node_second_macro mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying)
  rw [StringMacroCopyPrefixes.whole_prefix] at main nodes
  have source := transition_source_after_first mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying
  have rules := reached_inventory mode (transitionParams mode l) _ _ next (transition_current mode l _ _ source)
    (transition_bounded mode l _) first rest split
  exact from_all mode origin l _ g _ _ main (property_append mode _ _ _ nodes rules)

theorem second_restorations (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode
      (Joint mode origin l (values mode origin g node rule) g
        (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)++
          inventory mode (transitionParams mode l) (transitionTemplates mode l (values mode origin g node rule)) (transitionSpan mode)))
      (restoreForms mode (transitionParams mode l))
      (copied mode (transitionParams mode l) (Listing8CopyTrace.first mode l state)) := by
  have graph := current.body.state.head.graph
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have main := restore_slice mode (transitionParams mode l) _ _ (macros mode origin l t g node rule ctx old state current).2
  have nodes := restore_slice mode (transitionParams mode l) _ _
    (Listing8CopyOwnerLifetimeRun.node_second_macro mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying)
  have rules := Listing8CopyOwnerLifetimeRun.rule_restorations mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying
  have owners := StringTemplateStates.monotone mode _ _ _ _
    (fun reached pair => property_append mode _ _ reached.principal.memory pair.1 pair.2)
    (JointTemplateStates.join mode _ _ _ _ nodes rules)
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached pair => from_all mode origin l _ g _ reached pair.1 pair.2)
    (JointTemplateStates.join mode _ _ _ _ main owners)

theorem after_copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode
      (fun reached => Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g reached ∧
        Listing8JointOriginalGraphRetarget.Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointRetargetOwnerPhase.forms mode origin l t g node rule state) (Listing8MainCopies.finish mode l state) := by
  have graph := current.body.state.head.graph
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have actual := (Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx state graph.entry graph.forward image.prefixCurrent.copying).1
  have main := Listing8JointLocalMain.maintained mode origin l t g node rule ctx old state current
  rw [Listing8JointOriginalGraphMain.forms_shape,StringTemplateStates.append,StringWrites.trace_run_eq mode actual] at main
  exact JointTemplateStates.join mode _ _ _ _ main.2
    (Listing8JointOriginalGraphRetarget.maintained mode origin l t g node rule ctx old state current)

theorem copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode
      (fun reached => Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g reached ∧
        DwordTemplateCollection.All (Listing8CopyOwnerLifetimeRun.patches mode l) reached.principal.memory ∧
        ∀ template∈Listing8CopyOwnerLifetimeRun.patches mode l,DwordTemplateCollection.Decodes mode template reached.principal.memory)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have graph := current.body.state.head.graph
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have full := Listing8JointLocalMain.maintained mode origin l t g node rule ctx old state current
  rw [Listing8JointOriginalGraphMain.forms_shape,StringTemplateStates.append] at full
  have patch := Listing8CopyOwnerLifetimeRun.patches_copies mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached pair => ⟨pair.1,pair.2,fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (pair.2 template member)⟩)
    (JointTemplateStates.join mode _ _ _ _ full.1 patch)

/-- All copy lifetimes are supplied from the present maintained image: empty
before birth, exact byte-count inventory during MOVS, complete node inventory
through the entire second macro, and complete combined inventory in restoration.
The common original graph exception and every executable catalog use the SAME
state and ONE packet in each joint certificate. -/
structure Maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) : Prop where
  main : StringTemplateStates.Run mode (Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g)
    (Listing8LoopControl.program mode origin l t g node rule state) state
  firstMoves : ∀ first rest : List Nat,StringPlan.widths mode (nodeSpan mode)=first++rest →
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) first.sum)
      (StringMacroCopyPrefixes.reached mode (nodeParams mode l) state first)
  firstRestores : StringTemplateStates.Run mode
    (Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)))
    (restoreForms mode (nodeParams mode l)) (copied mode (nodeParams mode l) state)
  secondMacro : StringTemplateStates.Run mode
    (Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)))
    (macroForms mode (transitionParams mode l)) (Listing8CopyTrace.first mode l state)
  secondMoves : ∀ first rest : List Nat,StringPlan.widths mode (transitionSpan mode)=first++rest →
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)++
        inventory mode (transitionParams mode l) (transitionTemplates mode l (values mode origin g node rule)) first.sum)
      (StringMacroCopyPrefixes.reached mode (transitionParams mode l) (Listing8CopyTrace.first mode l state) first)
  secondRestores : StringTemplateStates.Run mode
    (Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)++
        inventory mode (transitionParams mode l) (transitionTemplates mode l (values mode origin g node rule)) (transitionSpan mode)))
    (restoreForms mode (transitionParams mode l)) (copied mode (transitionParams mode l) (Listing8CopyTrace.first mode l state))
  postCopies : StringTemplateStates.Run mode
    (fun reached => Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g reached ∧
      Listing8JointOriginalGraphRetarget.Property mode origin l (values mode origin g node rule) g reached.principal.memory)
    (Listing8JointRetargetOwnerPhase.forms mode origin l t g node rule state) (Listing8MainCopies.finish mode l state)
  copiesCatalog : StringTemplateStates.Run mode
    (fun reached => Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g reached ∧
      DwordTemplateCollection.All (Listing8CopyOwnerLifetimeRun.patches mode l) reached.principal.memory ∧
      ∀ template∈Listing8CopyOwnerLifetimeRun.patches mode l,DwordTemplateCollection.Decodes mode template reached.principal.memory)
    ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Maintained mode origin l t g node rule state :=
  ⟨Listing8JointLocalMain.maintained mode origin l t g node rule ctx old state current,
    first_moves mode origin l t g node rule ctx old state current,
    first_restorations mode origin l t g node rule ctx old state current,
    second_macro mode origin l t g node rule ctx old state current,
    second_moves mode origin l t g node rule ctx old state current,
    second_restorations mode origin l t g node rule ctx old state current,
    after_copies mode origin l t g node rule ctx old state current,
    copies mode origin l t g node rule ctx old state current⟩


@[expose] def setupForms (mode : Mode) (p : Params) :=
  (StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)
@[expose] def moveForms (mode : Mode) (widths : List Nat) :=
  (StringMoves.forms mode widths).map (StringWrites.liftString mode)

theorem restoration_start (mode : Mode) (p : Params) (state : StringExecution.State mode) :
    StringWrites.run mode (setupForms mode p++moveForms mode (StringPlan.widths mode p.size)) state=copied mode p state := by
  simp only [setupForms,moveForms,StringWrites.run_append,StringWrites.run_lift_string]
  rfl

theorem macro_endpoint (mode : Mode) (p : Params) (state : StringExecution.State mode) :
    StringWrites.run mode (macroForms mode p) state=finish mode p state := by
  rw [macroForms,StringWrites.run_lift_string,program_run]

theorem append_cut {α : Type} (first second before after : List α)
    (cut : first++second=before++after) :
    (∃ rest,first=before++rest) ∨ (∃ pre,before=first++pre ∧ second=pre++after) := by
  induction first generalizing before with
  | nil => exact Or.inr ⟨before,rfl,cut⟩
  | cons head tail ih =>
    cases before with
    | nil => exact Or.inl ⟨head::tail,rfl⟩
    | cons value rest =>
      have parts := List.cons.inj cut
      have same := parts.1
      subst value
      rcases ih rest parts.2 with ⟨remaining,location⟩ | ⟨pre,location,ending⟩
      · exact Or.inl ⟨remaining,congrArg (List.cons head) location⟩
      · exact Or.inr ⟨pre,congrArg (List.cons head) location,ending⟩

inductive BirthStage (mode : Mode) (p : Params) (templates : List (Template mode)) :
    List (StringStack.Form mode) → List (Template mode) → Prop where
  | setup (pre post) (cut : setupForms mode p=pre++post) : BirthStage mode p templates pre []
  | moves (first rest : List Nat) (split : StringPlan.widths mode p.size=first++rest) :
      BirthStage mode p templates (setupForms mode p++moveForms mode first) (inventory mode p templates first.sum)
  | restoration (pre post) (cut : restoreForms mode p=pre++post) :
      BirthStage mode p templates (setupForms mode p++moveForms mode (StringPlan.widths mode p.size)++pre)
        (inventory mode p templates p.size)

theorem macro_shape (mode : Mode) (p : Params) :
    macroForms mode p=setupForms mode p++(moveForms mode (StringPlan.widths mode p.size)++restoreForms mode p) := by
  simp only [macroForms,setupForms,moveForms,restoreForms,StringProgram.forms,List.map_append,List.append_assoc,sourceTail,destinationTail]

theorem birth_coverage (mode : Mode) (p : Params) (templates : List (Template mode))
    (before after : List (StringStack.Form mode)) (cut : macroForms mode p=before++after) :
    ∃ born,BirthStage mode p templates before born := by
  rw [macro_shape] at cut
  rcases append_cut _ _ before after cut with ⟨rest,split⟩ | ⟨pre,location,split⟩
  · exact ⟨[],BirthStage.setup before rest split⟩
  · rcases append_cut _ _ pre after split with ⟨rest,bodyCut⟩ | ⟨pre,bodyLocation,tailCut⟩
    · rcases StringCopyPrefixes.cut mode (StringPlan.widths mode p.size) _ _ bodyCut with ⟨first,last,widths,left,_⟩
      rw [location,left]
      exact ⟨inventory mode p templates first.sum,BirthStage.moves first last widths⟩
    · rw [location,bodyLocation,←List.append_assoc]
      exact ⟨inventory mode p templates p.size,BirthStage.restoration pre after tailCut⟩

@[expose] def Coverage (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (initial : StringExecution.State mode)
    (before : List (StringStack.Form mode)) : Prop :=
  (∃ born,BirthStage mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) before born) ∨
  (∃ pre born,before=macroForms mode (nodeParams mode l)++pre ∧
    BirthStage mode (transitionParams mode l) (transitionTemplates mode l (values mode origin g node rule)) pre born) ∨
  (∃ pre post,Listing8JointRetargetOwnerPhase.forms mode origin l t g node rule initial=pre++post ∧
    before=(Listing8MainCopies.program mode l).map (StringWrites.liftString mode)++pre)

theorem coverage (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (initial : StringExecution.State mode)
    (before after : List (StringStack.Form mode))
    (cut : Listing8LoopControl.program mode origin l t g node rule initial=before++after) :
    Coverage mode origin l t g node rule initial before := by
  rw [Listing8JointOriginalGraphMain.forms_shape] at cut
  rcases append_cut _ _ before after cut with ⟨rest,copyCut⟩ | ⟨pre,location,suffixCut⟩
  · have shape : (Listing8MainCopies.program mode l).map (StringWrites.liftString mode)=
        macroForms mode (nodeParams mode l)++macroForms mode (transitionParams mode l) := by
      simp only [Listing8MainCopies.program,Listing8CopyTrace.program,List.map_append,macroForms]
    rw [shape] at copyCut
    rcases append_cut _ _ before rest copyCut with ⟨rest,firstCut⟩ | ⟨pre,location,secondCut⟩
    · exact Or.inl (birth_coverage mode (nodeParams mode l) _ before rest firstCut)
    · obtain ⟨born,stage⟩ := birth_coverage mode (transitionParams mode l) _ pre rest secondCut
      exact Or.inr (Or.inl ⟨pre,born,location,stage⟩)
  · exact Or.inr (Or.inr ⟨pre,after,suffixCut,location⟩)

/-- One invariant indexed by the actual executed prefix. Static cuts specify
birth, never a future native state or a supplied copied image. Before copies
finish only the four existing patch headers are asserted. MOVS counts select
precisely the born fixed headers; setup/restoration retains earlier inventories.
After copies the live displacement catalog handles actual retarget mutation.
All fields bind the same reached memory, with one shared owner exception. -/
structure PrefixInvariant (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (initial : StringExecution.State mode)
    (before : List (StringStack.Form mode)) (reached : StringExecution.State mode) : Prop where
  phaseCoverage : Coverage mode origin l t g node rule initial before
  main : Listing8JointLocalMain.Property mode origin l (values mode origin g node rule) g reached
  patchHeaders : ∀ rest,(Listing8MainCopies.program mode l).map (StringWrites.liftString mode)=before++rest →
    DwordTemplateCollection.All (Listing8CopyOwnerLifetimeRun.patches mode l) reached.principal.memory ∧
    ∀ template∈Listing8CopyOwnerLifetimeRun.patches mode l,DwordTemplateCollection.Decodes mode template reached.principal.memory
  nodeBirth : ∀ first rest : List Nat,StringPlan.widths mode (nodeSpan mode)=first++rest →
    before=setupForms mode (nodeParams mode l)++moveForms mode first →
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) first.sum) reached
  nodeRestoration : ∀ pre post,restoreForms mode (nodeParams mode l)=pre++post →
    before=(setupForms mode (nodeParams mode l)++moveForms mode (StringPlan.widths mode (nodeSpan mode)))++pre →
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)) reached
  retainedNode : ∀ pre post,macroForms mode (transitionParams mode l)=pre++post →
    before=macroForms mode (nodeParams mode l)++pre →
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)) reached
  ruleBirth : ∀ first rest : List Nat,StringPlan.widths mode (transitionSpan mode)=first++rest →
    before=macroForms mode (nodeParams mode l)++(setupForms mode (transitionParams mode l)++moveForms mode first) →
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)++
        inventory mode (transitionParams mode l) (transitionTemplates mode l (values mode origin g node rule)) first.sum) reached
  ruleRestoration : ∀ pre post,restoreForms mode (transitionParams mode l)=pre++post →
    before=macroForms mode (nodeParams mode l)++((setupForms mode (transitionParams mode l)++
      moveForms mode (StringPlan.widths mode (transitionSpan mode)))++pre) →
    Joint mode origin l (values mode origin g node rule) g
      (inventory mode (nodeParams mode l) (nodeTemplates mode l (values mode origin g node rule)) (nodeSpan mode)++
        inventory mode (transitionParams mode l) (transitionTemplates mode l (values mode origin g node rule)) (transitionSpan mode)) reached
  retargeted : ∀ pre post,Listing8JointRetargetOwnerPhase.forms mode origin l t g node rule initial=pre++post →
    before=(Listing8MainCopies.program mode l).map (StringWrites.liftString mode)++pre →
    Listing8JointOriginalGraphRetarget.Property mode origin l (values mode origin g node rule) g reached.principal.memory

/-- The complete joint main predicate is derived at EVERY actual native
prefix from the present maintained image. All phase continuations use the
actual appended endpoint, including both restore helpers and CALL/return. -/
theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (before after : List (StringStack.Form mode))
    (cut : Listing8LoopControl.program mode origin l t g node rule state=before++after) :
    PrefixInvariant mode origin l t g node rule state before (StringWrites.run mode before state) := by
  have all := maintained mode origin l t g node rule ctx old state current
  refine ⟨coverage mode origin l t g node rule state before after cut,Listing8JointLocalMain.at_prefix mode origin l t g node rule ctx old state current before after cut,?_,?_,?_,?_,?_,?_,?_⟩
  · intro rest copyCut
    have kept := all.copiesCatalog
    rw [copyCut] at kept
    exact (StringTemplateStates.at_prefix mode _ before rest state kept).2
  · intro first rest split location
    rw [location]
    change Joint mode origin l (values mode origin g node rule) g _
      (StringWrites.run mode
        ((StringSetup.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination).map (StringWrites.liftString mode)++
          (StringMoves.forms mode first).map (StringWrites.liftString mode)) state)
    rw [StringMacroCopyPrefixes.whole_prefix]
    exact all.firstMoves first rest split
  · intro pre post split location
    rw [location,StringWrites.run_append]
    have begun : StringWrites.run mode (setupForms mode (nodeParams mode l)++moveForms mode (StringPlan.widths mode (nodeSpan mode))) state=
        copied mode (nodeParams mode l) state := restoration_start mode (nodeParams mode l) state
    rw [begun]
    have kept := all.firstRestores
    rw [split] at kept
    exact StringTemplateStates.at_prefix mode _ pre post _ kept
  · intro pre post split location
    rw [location,StringWrites.run_append,macro_endpoint]
    have kept := all.secondMacro
    rw [split] at kept
    exact StringTemplateStates.at_prefix mode _ pre post _ kept
  · intro first rest split location
    rw [location,StringWrites.run_append,macro_endpoint]
    change Joint mode origin l (values mode origin g node rule) g _
      (StringWrites.run mode
        ((StringSetup.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination).map (StringWrites.liftString mode)++
          (StringMoves.forms mode first).map (StringWrites.liftString mode)) (Listing8CopyTrace.first mode l state))
    rw [StringMacroCopyPrefixes.whole_prefix]
    exact all.secondMoves first rest split
  · intro pre post split location
    rw [location,StringWrites.run_append,macro_endpoint,StringWrites.run_append]
    have begun : StringWrites.run mode (setupForms mode (transitionParams mode l)++moveForms mode (StringPlan.widths mode (transitionSpan mode)))
        (finish mode (nodeParams mode l) state)=copied mode (transitionParams mode l) (finish mode (nodeParams mode l) state) :=
      restoration_start mode (transitionParams mode l) (finish mode (nodeParams mode l) state)
    rw [begun]
    have kept := all.secondRestores
    rw [split] at kept
    exact StringTemplateStates.at_prefix mode _ pre post _ kept
  · intro pre post split location
    rw [location,StringWrites.run_append]
    have graph := current.body.state.head.graph
    have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
    have actual := (Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx state graph.entry graph.forward image.prefixCurrent.copying).1
    rw [StringWrites.trace_run_eq mode actual]
    have kept := all.postCopies
    rw [split] at kept
    exact (StringTemplateStates.at_prefix mode _ pre post _ kept).2

end SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes
