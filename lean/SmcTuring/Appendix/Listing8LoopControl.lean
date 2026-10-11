module
public import SmcTuring.Appendix.Listing8LoopControlImage
public import SmcTuring.Appendix.Listing8JumpReturn

public section
namespace SmcTuring.Appendix.Listing8LoopControl
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Current:=Listing8LoopControlImage.Current
@[expose] def failureEnd (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8LoopFailure.failed mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8JumpReturn.finish mode origin (failed mode origin l t g node rule state) (failureEnd mode origin l t g node rule state)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  (Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous++
    Listing8JumpReturn.program mode origin (failed mode origin l t g node rule state)

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    Listing8JumpReturn.Current mode origin (failed mode origin l t g node rule state) (failureEnd mode origin l t g node rule state).principal.memory := by
  refine ⟨Listing8LoopControlImage.stack_packet mode origin l t g node rule ctx old state image,
    Listing8LoopControlImage.prefix_packet mode origin l t g node rule ctx old state image,Listing8LoopControlImage.call_packet mode origin l t g node rule ctx old state image,?_⟩
  cases selected : failed mode origin l t g node rule state
  · exact Listing8LoopControlImage.begin_packet mode origin l t g node rule ctx old state image
  · exact Listing8LoopControlImage.fail_packet mode origin l t g node rule ctx old state image

theorem entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    (failureEnd mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  rw [failureEnd,Listing8LoopFailure.endpoint mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.body.state.head.graph.entry image.body.state.head.graph.forward input]
  have position:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.jumpPC mode origin at position
  rw [position]

theorem target_capacity (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) (state : StringExecution.State mode) :
    Listing8JumpReturn.target mode origin (failed mode origin l t g node rule state)+Listing4TargetLayout.size mode<2^(8*mode.wordBytes) := by
  cases failed mode origin l t g node rule state
  · exact Listing4EntryLayout.target_capacity mode origin (Listing8GlobalBoot.entry_capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
  · exact Listing8FailLayout.capacity mode origin l (Listing8FullTableImage.start mode origin) (Listing8GraphNextFailImage.tail_bounds mode origin l t g node rule ctx)

theorem return_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    StringStack.Trace mode (failureEnd mode origin l t g node rule state) (Listing8JumpReturn.program mode origin (failed mode origin l t g node rule state)) (finish mode origin l t g node rule state) :=
  Listing8JumpReturn.trace mode origin (failed mode origin l t g node rule state) _ (entry mode origin l t g node rule ctx old state image)
    (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
    (target_capacity mode origin l t g node rule ctx state) (current mode origin l t g node rule ctx old state image)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state (program mode origin l t g node rule state) (finish mode origin l t g node rule state) :=
  StringStack.trace_append mode
    (Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
      (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.body)
    (return_trace mode origin l t g node rule ctx old state image)

theorem target_endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) (state : StringExecution.State mode) :
    Listing4TargetLayout.endPC mode (Listing8JumpReturn.target mode origin (failed mode origin l t g node rule state))=
      (if failed mode origin l t g node rule state then Listing8FullTableImage.start mode origin else l.start) := by
  cases failed mode origin l t g node rule state
  · have endpoint:=Listing4EntryLayout.endpoint mode origin
    change Listing4TargetLayout.endPC mode (Listing8BootImage.beginPC mode origin)=Listing4EntryLayout.mainPC mode origin at endpoint
    exact endpoint.trans ctx.boot.packed.symm
  · exact (Listing4TargetLayout.positions mode (Listing8JumpLayout.failPC mode origin)).2.2.2

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    finish mode origin l t g node rule state={failureEnd mode origin l t g node rule state with principal:={(failureEnd mode origin l t g node rule state).principal with
      pc:=Arithmetic.encodeNat mode (if failed mode origin l t g node rule state then Listing8FullTableImage.start mode origin else l.start),carry:=false}} := by
  rw [finish,Listing8JumpReturn.effect mode origin (failed mode origin l t g node rule state) _
    (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body) (current mode origin l t g node rule ctx old state image),
    target_endpoint mode origin l t g node rule ctx state,
    Listing4EntryValues.target_carry_clear mode origin (Listing8GlobalBoot.entry_capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)]

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (program mode origin l t g node rule state).length=(if mode=.x86 then 139 else 182) := by
  rw [program,List.length_append,List.length_map,Listing8LoopFailure.instruction_count,Listing8JumpReturn.instruction_count]
  cases mode <;> rfl

theorem memory (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    (finish mode origin l t g node rule state).principal.memory=(failureEnd mode origin l t g node rule state).principal.memory := by
  rw [effect mode origin l t g node rule ctx old state image]

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    (finish mode origin l t g node rule state).principal.stack=state.principal.stack ∧
    (finish mode origin l t g node rule state).sourceIndex=state.sourceIndex ∧
    (finish mode origin l t g node rule state).destinationIndex=state.destinationIndex ∧
    (finish mode origin l t g node rule state).backwards=false ∧
    (finish mode origin l t g node rule state).principal.carry=false ∧
    (finish mode origin l t g node rule state).principal.accumulator=(failureEnd mode origin l t g node rule state).principal.accumulator := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have prior:=Listing8LoopFailure.registers mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.body.state.head.graph.entry image.body.state.head.graph.forward input
  rw [effect mode origin l t g node rule ctx old state image]
  exact ⟨prior.1,prior.2.1,prior.2.2.1,prior.2.2.2.1,rfl,rfl⟩

theorem failed_iff (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    failed mode origin l t g node rule state=true ↔ Listing8GraphRun.Halted g node rule :=
  Listing8LoopGraphFailure.failed_iff mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
    (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.body ctx.native

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    (finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode
      (if failed mode origin l t g node rule state then Listing8FullTableImage.start mode origin else l.start) := by
  rw [effect mode origin l t g node rule ctx old state image]

end SmcTuring.Appendix.Listing8LoopControl
