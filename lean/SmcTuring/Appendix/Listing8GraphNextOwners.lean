module
public import SmcTuring.Appendix.Listing8GraphNextOwnerImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextOwners
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def ownerList (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) :=
  Listing8OwnerImage.owners mode (nextLayout mode origin l g node rule target) (liveValues mode origin g node rule target)
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8OwnerSequence.finish mode (ownerList mode origin l g node rule target)
    (Listing8GraphNextRetarget.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextRetarget.program mode origin l t g node rule target memory seed++
    ((Listing8OwnerSequence.program mode (ownerList mode origin l g node rule target)).map StringControl.Form.previous).map StringStack.Form.previous

theorem owner_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (Listing8GraphNextRetarget.finish mode origin l t g node rule target memory seed)
      (Listing8OwnerSequence.program mode (ownerList mode origin l g node rule target)) (finish mode origin l t g node rule target memory seed) := by
  have resources:=Listing8GraphNextCopies.resources mode origin l t g node rule target ctx
  have bounds:=Listing8GraphNextOwnerBounds.owner_bounds mode origin l t g node rule target ctx
  exact Listing8OwnerSequence.trace mode _ _ (Listing8CopiedOwners.chain mode _ _)
    (Listing8CopiedOwners.valid mode _ _ resources bounds) (Listing8CopiedOwners.outside mode _ _ resources bounds) _
    (Listing8GraphNextRetarget.registers mode origin l t g node rule target ctx selected memory seed).1
    (Listing8GraphNextOwnerImage.current mode origin l t g node rule target ctx selected memory seed)
/-- All four copied pointer owners and all three remaining scalar owners
execute in printed order on the same post-body/backedge memory. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextRetarget.trace mode origin l t g node rule target ctx selected memory seed)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (owner_trace mode origin l t g node rule target ctx selected memory seed)))
theorem result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=liveValues mode origin g node rule target
    let state:=Listing8GraphNextRetarget.finish mode origin l t g node rule target memory seed
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (codeEnd mode l) ∧
    (finish mode origin l t g node rule target memory seed).principal.memory=
      DwordCode.put (DwordCode.put (DwordCode.put state.principal.memory (Listing8LiteralInput.scalarField mode l.input) v.rule)
        (Listing8LiteralInput.updateStart mode l.input+6) v.fresh) (l.direction+6) v.direction ∧
    (finish mode origin l t g node rule target memory seed).principal.stack=state.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=state.principal.carry ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=state.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=state.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=state.backwards := by
  have resources:=Listing8GraphNextCopies.resources mode origin l t g node rule target ctx
  have bounds:=Listing8GraphNextOwnerBounds.owner_bounds mode origin l t g node rule target ctx
  have result:=Listing8OwnerSequence.result mode _ _ (Listing8CopiedOwners.chain mode _ _)
    (Listing8CopiedOwners.valid mode _ _ resources bounds) (Listing8CopiedOwners.outside mode _ _ resources bounds) _
    (Listing8GraphNextRetarget.registers mode origin l t g node rule target ctx selected memory seed).1
    (Listing8GraphNextOwnerImage.current mode origin l t g node rule target ctx selected memory seed)
  rw [Listing8CopiedOwners.endpoint] at result
  have codeSame : codeEnd mode (nextLayout mode origin l g node rule target)=codeEnd mode l := rfl
  have ruleSame : Listing8LiteralInput.scalarField mode (nextLayout mode origin l g node rule target).input=Listing8LiteralInput.scalarField mode l.input := rfl
  have freshSame : Listing8LiteralInput.updateStart mode (nextLayout mode origin l g node rule target).input=Listing8LiteralInput.updateStart mode l.input := rfl
  have dirSame : (nextLayout mode origin l g node rule target).direction=l.direction := rfl
  simpa only [finish,ownerList,Listing8OwnerImage.owners,Listing8OwnerSequence.writes,Listing8OwnerSequence.write,liveValues,
    codeSame,ruleSame,freshSame,dirSame] using result

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (codeEnd mode l) ∧
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false := by
  have actual:=result mode origin l t g node rule target ctx selected memory seed
  have prior:=Listing8GraphNextRetarget.registers mode origin l t g node rule target ctx selected memory seed
  exact ⟨actual.1,actual.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.1.trans prior.2.2.2.1,actual.2.2.2.2.2.2.trans prior.2.2.2.2.1,
    actual.2.2.2.1.trans prior.2.2.2.2.2⟩
theorem retained_image (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8OwnerSequence.Intact mode (ownerList mode origin l g node rule target) (finish mode origin l t g node rule target memory seed).principal.memory := by
  have resources:=Listing8GraphNextCopies.resources mode origin l t g node rule target ctx
  have bounds:=Listing8GraphNextOwnerBounds.owner_bounds mode origin l t g node rule target ctx
  exact Listing8OwnerSequence.retained_image mode _ _ (Listing8CopiedOwners.chain mode _ _)
    (Listing8CopiedOwners.valid mode _ _ resources bounds) (Listing8CopiedOwners.outside mode _ _ resources bounds) _
    (Listing8GraphNextRetarget.registers mode origin l t g node rule target ctx selected memory seed).1
    (Listing8GraphNextOwnerImage.current mode origin l t g node rule target ctx selected memory seed)
theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 216 else 266) := by
  have owners : (Listing8OwnerSequence.program mode (ownerList mode origin l g node rule target)).length=19 := by
    cases mode <;> simp [ownerList,Listing8OwnerSequence.program,Listing8OwnerImage.owners,Listing8OwnerSequence.forms,Listing8CopiedPointer.forms]
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextRetarget.instruction_count,owners]
  cases mode <;> rfl
theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 351 else 518) := by
  rw [(registers mode origin l t g node rule target ctx selected memory seed).1,
    Arithmetic.encode_nat_toNat mode _ (block_capacity mode l ctx.resources),
    (Listing8Initializer.code_geometry mode l).2.2,ctx.boot.packed]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega
theorem run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (nonhalt : ¬Listing8GraphRun.Halted g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ target : Fin g.transitions,Listing8GraphStep.nextRule g node rule=some target ∧
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
        (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) ∧
      (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 216 else 266) := by
  obtain ⟨target,selected⟩:=Listing8GraphLabels.nonhalt_rule g node rule nonhalt
  exact ⟨target,selected,trace mode origin l t g node rule target ctx selected memory seed,instruction_count mode origin l t g node rule target memory seed⟩

end SmcTuring.Appendix.Listing8GraphNextOwners
