module
public import SmcTuring.Appendix.Listing8LiveRetarget
public import SmcTuring.Appendix.Listing8GraphNextOwnerBounds

public section
namespace SmcTuring.Appendix.Listing8GraphNextRetarget
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def liveValues (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) :=
  values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8LiveRetarget.finish mode (nextLayout mode origin l g node rule target) (liveValues mode origin g node rule target)
    (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextCopies.program mode origin l t g node rule target memory seed++
    ((Listing8LiveRetarget.program mode (nextLayout mode origin l g node rule target) (liveValues mode origin g node rule target)).map
      StringControl.Form.previous).map StringStack.Form.previous

theorem retarget_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed)
      (Listing8LiveRetarget.program mode (nextLayout mode origin l g node rule target) (liveValues mode origin g node rule target))
      (finish mode origin l t g node rule target memory seed) :=
  Listing8LiveRetarget.trace mode _ _ (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx) _
    (Listing8GraphNextCopyFrames.registers mode origin l t g node rule target ctx selected memory seed).1
    (Listing8GraphPatchBlock.current mode origin l t g node rule target ctx selected memory seed)
/-- The actual next retargets and tape-owner execute directly after both
next copies. The original initializer appears only at the start of the trace. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextCopies.trace mode origin l t g node rule target ctx selected memory seed)
    (StringStack.previous_trace mode (StringControl.previous_trace mode
      (retarget_trace mode origin l t g node rule target ctx selected memory seed)))
theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next:=nextLayout mode origin l g node rule target
    let v:=liveValues mode origin g node rule target
    let state:=Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed
    finish mode origin l t g node rule target memory seed={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (backEntry mode (nodeParams mode next).destination)
      memory:=DwordCode.put (DwordRetargetSequence.writes mode (Listing8ModeOffsets.sites mode (patchLayout mode next)) state.principal.memory)
        (Listing8LiteralInput.sourceField mode next.input) v.tape}} :=
  Listing8LiveRetarget.effect mode _ _ (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)
    ctx.fields.tapeReach _ (Listing8GraphNextCopyFrames.registers mode origin l t g node rule target ctx selected memory seed).1
theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (backEntry mode (nodeParams mode l).destination) ∧
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false := by
  have prior:=Listing8GraphNextCopyFrames.registers mode origin l t g node rule target ctx selected memory seed
  rw [effect mode origin l t g node rule target ctx selected memory seed]
  exact ⟨rfl,prior.2.1,prior.2.2.1,prior.2.2.2.1,prior.2.2.2.2.1,prior.2.2.2.2.2⟩
theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 249 else 380) := by
  have cap:=block_capacity mode l ctx.resources
  have dests:=destinations mode l
  have small : backEntry mode (nodeParams mode l).destination<2^(8*mode.wordBytes) := by
    unfold backEntry; have span : 10≤nodeSpan mode := by unfold nodeSpan;omega
    omega
  rw [(registers mode origin l t g node rule target ctx selected memory seed).1,Arithmetic.encode_nat_toNat mode _ small]
  have geometry:=Listing8Initializer.code_geometry mode l
  rw [ctx.boot.packed] at geometry
  change patchStart mode l+50=origin+(if mode=.x86 then 249 else 380)
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] at geometry ⊢ <;> omega
theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 197 else 247) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextCopies.instruction_count,Listing8LiveRetarget.instruction_count]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8GraphNextRetarget
