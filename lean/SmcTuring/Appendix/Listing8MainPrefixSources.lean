module
public import SmcTuring.Appendix.Listing8MainPrefixFrames

public section
namespace SmcTuring.Appendix.Listing8MainPrefixSources
open Native Listing8CopyImage Listing8Prototypes Listing8MainPrefix

/-- The complete original node declaration is retained by an arbitrary
actual prefix. All exclusions are static addresses, not future byte facts. -/
theorem node_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (pointersOutside : ∀ writer∈Listing8PointerCopies.layouts mode l t,
      writer.destination+4≤l.sourceNode ∨ l.sourceNode+nodeSpan mode≤writer.destination)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory l.sourceNode (nodeSpan mode)=sourceNodeBytes mode l v := by
  have d:=destinations mode l
  have endInput:=code_to_input mode l b.resources
  have first : (nodeParams mode l).destination≤(transitionParams mode l).destination := by omega
  have inputAfter:=b.resources.inputAfter
  have mainBeforeInput : l.start≤l.input.start := by omega
  have nodeOutside:=b.resources.nodeOutside
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have cursor:=Listing8PointerCopies.cursor_before_patch mode l
  have cursorStart : l.start≤(Listing8PointerCopies.word mode l).destination := by
    have next:=endpoint_lower mode l.start (nodeSpan mode)
    change l.start≤secondStart mode l at next
    simp only [Listing8PointerCopies.word,StringCodec.sourceField];omega
  have afterPatch:= (coordinates mode l).2.2
  have patchBefore : l.start≤patchStart mode l := by
    have first:=endpoint_lower mode l.start (nodeSpan mode)
    have next:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
    change l.start≤secondStart mode l at first
    change secondStart mode l≤patchStart mode l at next
    omega
  rw [Listing8MainPrefixFrames.window mode l t v b state entry forward current _ _
    (by rcases nodeOutside with early | late; exact Or.inr (by omega); exact Or.inl (by omega))
    (by rcases nodeOutside with early | late; exact Or.inr (by omega); exact Or.inl (by omega))
    (fun site member => by
      have bounds:=Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
      change patchStart mode l+40≤site.owner ∧ site.owner+10≤Listing8ModeOffsets.endPC mode (patchLayout mode l) ∧ _ at bounds
      change _ ∧ site.owner+10≤codeEnd mode l ∧ _ at bounds
      rcases nodeOutside with early | late
      · exact Or.inr (by omega)
      · exact Or.inl (by omega))
    (by rcases nodeOutside with early | late; exact Or.inr (by omega); exact Or.inl (by omega))
    (by rcases nodeOutside with early | late; exact Or.inr (by omega); exact Or.inl (by omega))
    (by rcases nodeOutside with early | late; exact Or.inr (by omega); exact Or.inl (by omega))
    (Or.symm b.owners.nodeDirection)
    (by rcases nodeOutside with early | late; exact Or.inr (by omega); exact Or.inl (by omega))
    pointersOutside]
  exact current.copying.node

theorem tape_symbol (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (pointersOutside : ∀ writer∈Listing8PointerCopies.layouts mode l t,
      writer.destination+4≤l.sourceNode ∨ l.sourceNode+nodeSpan mode≤writer.destination)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    DwordCode.get (finish mode l t v state).principal.memory (l.input.head+6)=v.tape := by
  rw [b.fields.headLabel]
  apply (node_values mode l.sourceNode v.tape v.back v.forward _ ?_).1
  simpa only [sourceNodeBytes,node_length] using node_current mode l t v b pointersOutside state entry forward current

end SmcTuring.Appendix.Listing8MainPrefixSources
