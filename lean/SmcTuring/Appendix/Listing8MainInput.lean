module
public import SmcTuring.Appendix.Listing8MainInputImage
public import SmcTuring.Appendix.Listing8MainPrefixSources
public import SmcTuring.Appendix.Listing8InputReuse
public import SmcTuring.Appendix.Listing8InputMaskEffects
public import SmcTuring.Native.StringMixed

public section
namespace SmcTuring.Appendix.Listing8MainInput
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInputImage.OldInput
abbrev Current:=Listing8MainInputImage.Current
structure Bounds (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) : Prop where
  input : Listing8MainInputImage.Bounds mode l t v
  pointersOutside : ∀ writer∈Listing8PointerCopies.layouts mode l t,
    writer.destination+4≤l.sourceNode ∨ l.sourceNode+Listing8Prototypes.nodeSpan mode≤writer.destination
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  let ready:=Listing8MainPrefix.finish mode l t v state
  {ready with principal:=Listing8LiteralComposition.finish mode l.input v.rule v.tape v.fresh ready.principal}
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  Listing8MainPrefix.program mode l t v++(Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh).map (StringMixed.canonical mode)

/-- Actual printed input interleaving on an arbitrary current main entry;
reset, comparison, both mask-copy calls and tape update have derived fetches. -/
theorem input_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode (Listing8MainPrefix.finish mode l t v state)
      ((Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh).map (StringMixed.canonical mode))
      (finish mode l t v state) := by
  have fields:=b.input.prefixBounds.fields
  have masks:=Listing8InputBounds.masks mode l fields
  have update:=Listing8InputBounds.update mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have outside:=Listing8InputBounds.outside mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have atInput:=Listing8MainPrefix.entry mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have image:=Listing8MainInputImage.current mode l t v old b.input state entry forward current
  have cursor:=Listing8MainPrefixFrames.head_cursor mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  exact StringMixed.trace mode _ _ _ (Listing8InputMask.trace mode l.input v.rule v.tape old.pending v.fresh old.mask
    b.input.prefixBounds.resources.inputFits masks update outside _ atInput image cursor)

theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode state (program mode l t v) (finish mode l t v state) :=
  StringDword.trace_append mode (Listing8MainPrefix.trace mode l t v b.input.prefixBounds state entry forward current.prefixCurrent)
    (input_trace mode l t v old b state entry forward current)

theorem stack_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringStack.Trace mode state (((program mode l t v).map StringControl.Form.previous).map StringStack.Form.previous)
      (finish mode l t v state) :=
  StringStack.previous_trace mode (StringControl.previous_trace mode (trace mode l t v old b state entry forward current))

theorem tape_value (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    DwordCode.get (finish mode l t v state).principal.memory (l.input.head+6)=
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  have fields:=b.input.prefixBounds.fields
  have masks:=Listing8InputBounds.masks mode l fields
  have update:=Listing8InputBounds.update mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have outside:=Listing8InputBounds.outside mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have atInput:=Listing8MainPrefix.entry mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have image:=Listing8MainInputImage.current mode l t v old b.input state entry forward current
  have cursor:=Listing8MainPrefixFrames.head_cursor mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have value:=Listing8MainPrefixSources.tape_symbol mode l t v b.input.prefixBounds b.pointersOutside state entry forward current.prefixCurrent
  exact Listing8InputMask.tape_value mode l.input v.rule v.tape old.pending v.fresh old.mask
    b.input.prefixBounds.resources.inputFits masks update outside (Listing8MainPrefix.finish mode l t v state).principal
    atInput image cursor value

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    (finish mode l t v state).principal.pc=Arithmetic.encodeNat mode (Listing8LiteralInput.endPC mode l.input) := by
  have fields:=b.input.prefixBounds.fields
  have masks:=Listing8InputBounds.masks mode l fields
  have update:=Listing8InputBounds.update mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have outside:=Listing8InputBounds.outside mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have atInput:=Listing8MainPrefix.entry mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have image:=Listing8MainInputImage.current mode l t v old b.input state entry forward current
  have cursor:=Listing8MainPrefixFrames.head_cursor mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have value:=Listing8MainPrefixSources.tape_symbol mode l t v b.input.prefixBounds b.pointersOutside state entry forward current.prefixCurrent
  exact Listing8InputMaskEffects.endpoint mode l.input v.rule v.tape old.pending v.fresh old.mask
    b.input.prefixBounds.resources.inputFits masks update outside (Listing8MainPrefix.finish mode l t v state).principal
    atInput image cursor value

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    (finish mode l t v state).principal.stack=state.principal.stack ∧
    (finish mode l t v state).sourceIndex=state.sourceIndex ∧
    (finish mode l t v state).destinationIndex=state.destinationIndex ∧
    (finish mode l t v state).backwards=false ∧
    (finish mode l t v state).principal.carry=false ∧
    (finish mode l t v state).principal.accumulator=
      DwordCode.lift mode (DwordCode.low mode (Listing8MainPrefix.finish mode l t v state).principal.accumulator) := by
  have fields:=b.input.prefixBounds.fields
  have masks:=Listing8InputBounds.masks mode l fields
  have update:=Listing8InputBounds.update mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have outside:=Listing8InputBounds.outside mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have atInput:=Listing8MainPrefix.entry mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have image:=Listing8MainInputImage.current mode l t v old b.input state entry forward current
  have cursor:=Listing8MainPrefixFrames.head_cursor mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have value:=Listing8MainPrefixSources.tape_symbol mode l t v b.input.prefixBounds b.pointersOutside state entry forward current.prefixCurrent
  have actual:=Listing8InputMaskEffects.registers mode l.input v.rule v.tape old.pending v.fresh old.mask
    b.input.prefixBounds.resources.inputFits masks update outside (Listing8MainPrefix.finish mode l t v state).principal
    atInput image cursor value
  have prior:=Listing8MainPrefix.registers mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  exact ⟨actual.2.1.trans prior.1,prior.2.1,prior.2.2.1,prior.2.2.2.1,actual.2.2,actual.1⟩

theorem retained_image (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8InputMask.Intact mode l.input (-(v.rule-v.tape)) v.tape
      (CursorEffects.delta v.tape v.fresh (Listing8LiteralInput.chosen v.rule v.tape)) v.fresh
      (InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape)) (finish mode l t v state).principal.memory := by
  have fields:=b.input.prefixBounds.fields
  have masks:=Listing8InputBounds.masks mode l fields
  have update:=Listing8InputBounds.update mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have outside:=Listing8InputBounds.outside mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have atInput:=Listing8MainPrefix.entry mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have image:=Listing8MainInputImage.current mode l t v old b.input state entry forward current
  have cursor:=Listing8MainPrefixFrames.head_cursor mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have value:=Listing8MainPrefixSources.tape_symbol mode l t v b.input.prefixBounds b.pointersOutside state entry forward current.prefixCurrent
  exact Listing8InputReuse.completed_image mode l.input v.rule v.tape old.pending v.fresh old.mask
    b.input.prefixBounds.resources.inputFits masks update outside (Listing8MainPrefix.finish mode l t v state).principal
    atInput image cursor value

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    (program mode l t v).length=(if mode=.x86 then 101 else 118) := by
  rw [program,List.length_append,List.length_map,Listing8MainPrefix.instruction_count,Listing8LiteralComposition.instruction_count]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8MainInput
