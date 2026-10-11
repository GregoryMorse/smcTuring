module
public import SmcTuring.Appendix.Listing8GraphBackedgeValues

public section
namespace SmcTuring.Appendix.Listing8GraphCopyResources
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- Rebind only the next pass's logical source labels. Macro placement,
copied destinations and scalar/control field positions are unchanged. -/
@[expose] def rebound (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) : Layout :=
  {l with
    sourceNode:=nodePC mode origin g node
    sourceTransition:=rulePC mode origin g rule
    input:={l.input with head:=nodePC mode origin g node}}

theorem input_before_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LiteralInput.endPC mode l.input≤Listing8FullTableImage.start mode origin := by
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  rw [ctx.boot.packed] at input
  rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] at input ⊢ <;> omega
theorem input_before_node (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) (query : Fin g.nodes) :
    Listing8LiteralInput.endPC mode l.input≤nodePC mode origin g query :=
  Nat.le_trans (input_before_table mode origin l t g node rule ctx) (Listing8GraphOwnerBounds.node_after_table mode origin g query)
theorem input_before_rule (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) (query : Fin g.transitions) :
    Listing8LiteralInput.endPC mode l.input≤rulePC mode origin g query :=
  Nat.le_trans (input_before_table mode origin l t g node rule ctx) (Listing8GraphLayout.transition_lower mode origin query.val)

/-- Retargeting a copy source after its macro and destination needs only
derived initial layout bounds, never future code or readiness. -/
theorem source_resources (mode : Mode) (p : StringMacroLayout.Params) (r : TemplateCopy.Resources mode p) (source : Nat)
    (fits : source+max p.size mode.wordBytes<2^(8*mode.wordBytes))
    (after : StringMacroLayout.endpoint mode p≤source) (apart : p.destination+p.size≤source) :
    TemplateCopy.Resources mode {p with source:=source} :=
  ⟨r.sizeFits,r.codeFits,fits,r.destinationFits,Or.inr apart,Or.inr after,r.destinationOutside⟩

theorem resources (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (nextNode : Fin g.nodes) (nextRule : Fin g.transitions) :
    Resources mode (rebound mode origin l g nextNode nextRule) := by
  have endInput:=code_to_input mode l ctx.resources
  have nodeAfter:=input_before_node mode origin l t g node rule ctx nextNode
  have ruleAfter:=input_before_rule mode origin l t g node rule ctx nextRule
  have parts:=coordinates mode l
  have firstLower:=endpoint_lower mode l.start (nodeSpan mode)
  have secondLower:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  have dests:=destinations mode l
  have nodeFits:=Listing8GraphLayout.node_capacity mode origin g.transitions g.nodes nextNode.val ctx.native nextNode.isLt
  have ruleFits:=Listing8GraphLayout.transition_capacity mode origin g.transitions g.nodes nextRule.val ctx.native nextRule.isLt
  have nodeLarge : mode.wordBytes≤nodeSpan mode := by cases mode <;> decide
  have ruleLarge : mode.wordBytes≤transitionSpan mode := by cases mode <;> decide
  change nodePC mode origin g nextNode+nodeSpan mode<_ at nodeFits
  change rulePC mode origin g nextRule+transitionSpan mode<_ at ruleFits
  refine ⟨?_,?_,ctx.resources.inputAfter,ctx.resources.inputFits,Or.inr nodeAfter,Or.inr ruleAfter,Or.inr ?_⟩
  · change TemplateCopy.Resources mode {(nodeParams mode l) with source:=nodePC mode origin g nextNode}
    apply source_resources mode _ ctx.resources.node
    · simpa only [nodeParams,Nat.max_eq_left nodeLarge] using nodeFits
    · change secondStart mode l≤nodePC mode origin g nextNode
      omega
    · change (nodeParams mode l).destination+nodeSpan mode≤nodePC mode origin g nextNode
      omega
  · change TemplateCopy.Resources mode {(transitionParams mode l) with source:=rulePC mode origin g nextRule}
    apply source_resources mode _ ctx.resources.transition
    · simpa only [transitionParams,Nat.max_eq_left ruleLarge] using ruleFits
    · change patchStart mode l≤rulePC mode origin g nextRule
      omega
    · change (transitionParams mode l).destination+transitionSpan mode≤rulePC mode origin g nextRule
      omega
  · exact Listing8GraphLayout.table_node_apart mode origin g.transitions nextRule.val nextNode.val nextRule.isLt

end SmcTuring.Appendix.Listing8GraphCopyResources
