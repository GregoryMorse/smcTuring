module
public import SmcTuring.Appendix.Listing8GraphResetNodes

public section
namespace SmcTuring.Appendix.Listing8GraphInputRun
open Native Listing8SourceGraph Listing8GraphInputContext Listing8GraphBodyNodes
@[expose] def program (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphRun.program mode origin l t g node rule memory seed++
    ((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g node rule)).map
      StringControl.Form.previous).map StringStack.Form.previous
@[expose] def finish (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8NodeTrace.finish mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g node rule)
    (Listing8GraphRun.finish mode origin l t g node rule memory seed)

theorem entry (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8GraphLayout.input mode origin g.transitions) := by
  rw [Listing8GraphRun.finish,Listing8FullTableReset.effect mode origin l t (values mode origin g node rule) _
    (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx),
    Listing8GraphReset.actual_region mode origin l t _ (table mode origin g) ctx.boot ctx.body,
    Listing8GraphReset.endpoint,table_length]

/-- All printed original input declarations follow the actual reset in the
same continuously evolving state. Their packets come from derived live bytes. -/
theorem trace (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (halted : Listing8GraphRun.Halted g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphRun.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) := by
  have first:=Listing8GraphRun.run mode origin l t g node rule ctx.nodeLocated ctx.ruleLocated ctx.resources ctx.fields
    ctx.copies ctx.boot ctx.body ctx.native halted memory seed |>.1
  have last:=StringStack.previous_trace mode (StringControl.previous_trace mode
    (Listing8NodeTrace.trace mode _ _ (Listing8GraphResetNodes.valid mode origin g node rule ctx.native) _
      (entry mode origin l t g node rule ctx memory seed) (Listing8GraphResetNodes.initial mode origin l t g node rule ctx memory seed)))
  exact StringStack.trace_append mode first last

theorem result (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) ∧
    (finish mode origin l t g node rule memory seed).principal.memory=(Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory ∧
    (finish mode origin l t g node rule memory seed).principal.stack=(Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.stack ∧
    (finish mode origin l t g node rule memory seed).principal.carry=(Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.carry ∧
    (finish mode origin l t g node rule memory seed).sourceIndex=(Listing8GraphRun.finish mode origin l t g node rule memory seed).sourceIndex ∧
    (finish mode origin l t g node rule memory seed).destinationIndex=(Listing8GraphRun.finish mode origin l t g node rule memory seed).destinationIndex ∧
    (finish mode origin l t g node rule memory seed).backwards=(Listing8GraphRun.finish mode origin l t g node rule memory seed).backwards := by
  have actual:=Listing8NodeTrace.result mode _ _ (Listing8GraphResetNodes.valid mode origin g node rule ctx.native) _
    (entry mode origin l t g node rule ctx memory seed) (Listing8GraphResetNodes.initial mode origin l t g node rule ctx memory seed)
  have endpoint : Listing8NodeTable.endPC mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g node rule)=
      Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
    simp only [Listing8NodeTable.endPC,length];rfl
  rw [endpoint] at actual
  exact actual

theorem instruction_count (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=(if mode=.x86 then 156 else 207)+11*g.transitions+9*g.nodes := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphRun.program,
    Listing8FullTableReset.instruction_count,table_length,Listing8NodeTrace.instruction_count,length]

theorem endpoint (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc.toNat=
      Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  rw [(result mode origin l t g node rule ctx memory seed).1]
  exact Arithmetic.encode_nat_toNat mode _ ctx.native.capacity
end SmcTuring.Appendix.Listing8GraphInputRun
