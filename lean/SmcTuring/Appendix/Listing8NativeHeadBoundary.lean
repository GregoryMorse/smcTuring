module
public import SmcTuring.Appendix.Listing8LoopInterpreter
public import SmcTuring.Native.StringTracePrefixes

public section
namespace SmcTuring.Appendix.Listing8NativeHeadBoundary
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- Decode the actual cursor word using the declared packed tape origin.
The observation boundary is before the printed cursor reset. -/
@[expose] def observe (mode : Mode) (origin : Nat) (lower : Int) (transitions cursor : Nat)
    (memory : ByteMemory.Memory) : Int :=
  lower+(((MixedMemory.getWord mode memory cursor).toNat-Listing8GraphLayout.input mode origin transitions)/nodeSpan mode : Nat)

theorem pointer_position (mode : Mode) (origin : Nat) (lower : Int) (g : Graph) (index : Fin g.nodes)
    (cursor : Nat) (memory : ByteMemory.Memory) (fits : nodePC mode origin g index<2^(8*mode.wordBytes))
    (pointer : MixedMemory.getWord mode memory cursor=Arithmetic.encodeNat mode (nodePC mode origin g index)) :
    observe mode origin lower g.transitions cursor memory=lower+(index.val : Int) := by
  rw [observe,pointer,Arithmetic.encode_nat_toNat mode _ fits]
  cases mode <;> simp [nodePC,Listing8GraphLayout.node,nodeSpan,pointerSpan,ReaderImage.totalSize]

theorem after_failure (mode : Mode) (origin : Nat) (lower : Int) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    observe mode origin lower g.transitions l.input.cursor
      (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.memory=
        lower+((Listing8GraphStep.nextNode g node rule).val : Int) := by
  have pointer:=Listing8LoopGraphFailure.logical_head mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
    (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.body
  have capacity:=Listing8GraphPointers.node_capacity mode origin g (Listing8GraphStep.nextNode g node rule) ctx.native
  rw [observe,Listing8LoopControl.failureEnd,pointer,Arithmetic.encode_nat_toNat mode _ (by omega)]
  cases mode <;> simp [nodePC,Listing8GraphLayout.node,nodeSpan,pointerSpan,ReaderImage.totalSize]

theorem terminal_cut (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    ∃ later,Listing8LoopTerminal.program mode origin l t g node rule state=
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous)++later := by
  unfold Listing8LoopTerminal.program Listing8LoopReset.program Listing8LoopTable.program Listing8LoopControl.program
  simp only [List.append_assoc]
  exact ⟨_,rfl⟩

/-- Both trace pieces are derived from one actual terminal execution. The
observed native word is read from its reached boundary memory. -/
theorem terminal (mode : Mode) (origin : Nat) (lower : Int) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    ∃ later,
      Listing8LoopTerminal.program mode origin l t g node rule state=
        ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
          (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous)++later ∧
      StringStack.Trace mode state
        ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
          (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous)
        (Listing8LoopControl.failureEnd mode origin l t g node rule state) ∧
      StringStack.Trace mode (Listing8LoopControl.failureEnd mode origin l t g node rule state) later
        (Listing8LoopTerminal.finish mode origin l t g node rule state) ∧
      observe mode origin lower g.transitions l.input.cursor
        (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.memory=
          lower+((Listing8GraphStep.nextNode g node rule).val : Int) := by
  obtain ⟨later,cut⟩:=terminal_cut mode origin l t g node rule state
  have first:=Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
    (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.control.body
  have whole:=Listing8LoopTerminal.trace mode origin l t g node rule ctx old state image halted
  rw [cut] at whole
  exact ⟨later,cut,first,StringTracePrefixes.tail mode _ later state _ _ whole first,
    after_failure mode origin lower l t g node rule ctx old state image.control⟩

theorem iterations (mode : Mode) (origin : Nat) (lower : Int) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (l : Layout) (old : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) :
    ∃ (cursor : Nat) (boundary finalState : StringExecution.State mode) (before after : List (StringStack.Form mode)),
      StringStack.Trace mode state before boundary ∧ StringStack.Trace mode boundary after finalState ∧
      StringStack.Trace mode state (before++after) finalState ∧
      observe mode origin lower lastGraph.transitions cursor boundary.principal.memory=
        lower+((Listing8GraphStep.nextNode lastGraph lastNode lastRule).val : Int) := by
  obtain ⟨lastL,lastOld,lastState,code,lastCtx,lastImage,actual,length,stack,source,destination⟩:=
    Listing8LoopHaltIteration.execute mode origin t logical l old state ctx image
  obtain ⟨later,cut,first,tail,head⟩:=terminal mode origin lower lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have reached:=StringStack.trace_append mode actual first
  exact ⟨lastL.input.cursor,Listing8LoopControl.failureEnd mode origin lastL t lastGraph lastNode lastRule lastState,
    Listing8LoopTerminal.finish mode origin lastL t lastGraph lastNode lastRule lastState,_,later,
    reached,tail,StringStack.trace_append mode reached tail,head⟩

end SmcTuring.Appendix.Listing8NativeHeadBoundary
