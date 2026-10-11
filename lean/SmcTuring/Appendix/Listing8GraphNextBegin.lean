module
public import SmcTuring.Appendix.Listing8GraphNextJump
public import SmcTuring.Appendix.Listing8JumpReturn

public section
namespace SmcTuring.Appendix.Listing8GraphNextBegin
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8JumpReturn.finish mode origin false (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextFailure.program mode origin l t g node rule target memory seed++Listing8JumpReturn.program mode origin false

theorem nonfailure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed=false := by
  cases result : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · rfl
  · exact False.elim (nonhalt ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp result))

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8JumpReturn.Current mode origin false (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory := by
  refine ⟨Listing8GraphNextStackImage.stack_packet mode origin l t g node rule target ctx selected memory seed,
    Listing8GraphNextStackImage.jump_prefix mode origin l t g node rule target ctx selected memory seed,?_,
    Listing8GraphNextStackImage.begin_packet mode origin l t g node rule target ctx selected memory seed⟩
  have packet:=Listing8GraphNextJump.call_packet mode origin l t g node rule target ctx selected memory seed
  rw [nonfailure mode origin l t g node rule target ctx selected memory seed nonhalt] at packet
  exact packet

theorem return_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    StringStack.Trace mode (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed)
      (Listing8JumpReturn.program mode origin false) (finish mode origin l t g node rule target memory seed) :=
  Listing8JumpReturn.trace mode origin false _ (Listing8GraphNextJump.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8JumpImage.capacity mode origin l t _ ctx.boot ctx.body)
    (Listing4EntryLayout.target_capacity mode origin (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
    (current mode origin l t g node rule target ctx selected memory seed nonhalt)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextFailure.trace mode origin l t g node rule target ctx selected memory seed)
    (return_trace mode origin l t g node rule target ctx selected memory seed nonhalt)

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    let state:=Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed
    finish mode origin l t g node rule target memory seed={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode l.start,carry:=false}} := by
  rw [finish,Listing8JumpReturn.effect mode origin false _ (Listing8JumpImage.capacity mode origin l t _ ctx.boot ctx.body)
    (current mode origin l t g node rule target ctx selected memory seed nonhalt)]
  change {Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed with principal:={
    (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal with
    pc:=Arithmetic.encodeNat mode (Listing4TargetLayout.endPC mode (Listing8BootImage.beginPC mode origin)),carry:=Listing4TargetEffects.flag mode origin}}=_
  have endpoint:=Listing4EntryLayout.endpoint mode origin
  change Listing4TargetLayout.endPC mode (Listing8BootImage.beginPC mode origin)=Listing4EntryLayout.mainPC mode origin at endpoint
  rw [endpoint,←ctx.boot.packed,
    Listing4EntryValues.target_carry_clear mode origin (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)]

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 286 else 377) := by
  rw [program,List.length_append,Listing8GraphNextFailure.instruction_count,Listing8JumpReturn.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode l.start ∧
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).principal.accumulator=(Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.accumulator := by
  have prior:=Listing8GraphNextFailure.registers mode origin l t g node rule target ctx selected memory seed
  rw [effect mode origin l t g node rule target ctx selected memory seed nonhalt]
  exact ⟨rfl,prior.1,prior.2.1,prior.2.2.1,prior.2.2.2.1,rfl,rfl⟩

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 52 else 97) := by
  rw [(registers mode origin l t g node rule target ctx selected memory seed nonhalt).1,ctx.boot.packed,
    Arithmetic.encode_nat_toNat mode _ (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)]
  cases mode <;> rfl

theorem transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) := by
  rw [effect mode origin l t g node rule target ctx selected memory seed nonhalt]
  exact Listing8GraphNextFailureFrames.transition mode origin l t g node rule target ctx selected memory seed

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) := by
  rw [effect mode origin l t g node rule target ctx selected memory seed nonhalt]
  exact Listing8GraphNextFailureFrames.head mode origin l t g node rule target ctx selected memory seed

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphNextInputNodes.graph g node rule target))
      (finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  rw [effect mode origin l t g node rule target ctx selected memory seed nonhalt]
  exact Listing8GraphNextFailureFrames.source_graph mode origin l t g node rule target ctx selected memory seed

theorem failure_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  rw [effect mode origin l t g node rule target ctx selected memory seed nonhalt]
  exact Listing8FailureReuseEffects.current_after mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)

theorem code_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin := by
  rw [effect mode origin l t g node rule target ctx selected memory seed nonhalt]
  exact Listing8GraphNextStackImage.code_current mode origin l t g node rule target ctx selected memory seed

theorem control_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8JumpReturn.Current mode origin false (finish mode origin l t g node rule target memory seed).principal.memory :=
  Listing8JumpReturn.current_after mode origin false _ (Listing8JumpImage.capacity mode origin l t _ ctx.boot ctx.body)
    (current mode origin l t g node rule target ctx selected memory seed nonhalt)

end SmcTuring.Appendix.Listing8GraphNextBegin
