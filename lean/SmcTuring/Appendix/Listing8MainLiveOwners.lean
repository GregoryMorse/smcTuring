module
public import SmcTuring.Appendix.Listing8MainRetarget
public import SmcTuring.Appendix.Listing8CopiedOwners

public section
namespace SmcTuring.Appendix.Listing8MainLiveOwners
open Native Listing8CopyImage Listing8Prototypes Listing8MainCopyImage
@[expose] def finish (mode : Mode) (l : Layout) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8OwnerSequence.finish mode (Listing8OwnerImage.owners mode l v) (Listing8MainRetarget.finish mode l v state)
@[expose] def program (mode : Mode) (l : Layout) (v : Values mode) :=
  Listing8MainRetarget.program mode l v++Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l v)

theorem owner_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    StringDword.Trace mode (Listing8MainRetarget.finish mode l v state)
      (Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l v)) (finish mode l v state) :=
  Listing8OwnerSequence.trace mode _ _ (Listing8CopiedOwners.chain mode l v)
    (Listing8CopiedOwners.valid mode l v r b) (Listing8CopiedOwners.outside mode l v r b) _
    (Listing8MainRetarget.registers mode l v r reach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l v r reach state entry forward current)

theorem trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    StringDword.Trace mode state (program mode l v) (finish mode l v state) :=
  StringDword.trace_append mode (Listing8MainRetarget.trace mode l v r state entry forward current)
    (owner_trace mode l v r b reach state entry forward current)

theorem result (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    let retargeted:=Listing8MainRetarget.finish mode l v state
    (finish mode l v state).principal.pc=Arithmetic.encodeNat mode (codeEnd mode l) ∧
    (finish mode l v state).principal.memory=
      DwordCode.put (DwordCode.put (DwordCode.put retargeted.principal.memory (Listing8LiteralInput.scalarField mode l.input) v.rule)
        (Listing8LiteralInput.updateStart mode l.input+6) v.fresh) (l.direction+6) v.direction ∧
    (finish mode l v state).principal.stack=retargeted.principal.stack ∧
    (finish mode l v state).principal.carry=retargeted.principal.carry ∧
    (finish mode l v state).sourceIndex=retargeted.sourceIndex ∧
    (finish mode l v state).destinationIndex=retargeted.destinationIndex ∧
    (finish mode l v state).backwards=retargeted.backwards := by
  have actual:=Listing8OwnerSequence.result mode _ _ (Listing8CopiedOwners.chain mode l v)
    (Listing8CopiedOwners.valid mode l v r b) (Listing8CopiedOwners.outside mode l v r b) _
    (Listing8MainRetarget.registers mode l v r reach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l v r reach state entry forward current)
  rw [Listing8CopiedOwners.endpoint] at actual
  simpa only [finish,Listing8OwnerImage.owners,Listing8OwnerSequence.writes,Listing8OwnerSequence.write] using actual

theorem registers (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    (finish mode l v state).principal.pc=Arithmetic.encodeNat mode (codeEnd mode l) ∧
    (finish mode l v state).principal.stack=state.principal.stack ∧
    (finish mode l v state).sourceIndex=state.sourceIndex ∧
    (finish mode l v state).destinationIndex=state.destinationIndex ∧
    (finish mode l v state).backwards=false ∧ (finish mode l v state).principal.carry=false := by
  have actual:=result mode l v r b reach state entry forward current
  have prior:=Listing8MainRetarget.registers mode l v r reach state entry forward current
  exact ⟨actual.1,actual.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.1.trans prior.2.2.2.1,actual.2.2.2.2.2.2.trans prior.2.2.2.2.1,
    actual.2.2.2.1.trans prior.2.2.2.2.2⟩

theorem retained_image (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    Listing8OwnerSequence.Intact mode (Listing8OwnerImage.owners mode l v) (finish mode l v state).principal.memory :=
  Listing8OwnerSequence.retained_image mode _ _ (Listing8CopiedOwners.chain mode l v)
    (Listing8CopiedOwners.valid mode l v r b) (Listing8CopiedOwners.outside mode l v r b) _
    (Listing8MainRetarget.registers mode l v r reach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l v r reach state entry forward current)

theorem window (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) (observed count : Nat)
    (nodeOutside : (nodeParams mode l).destination+nodeSpan mode≤observed ∨ observed+count≤(nodeParams mode l).destination)
    (ruleOutside : (transitionParams mode l).destination+transitionSpan mode≤observed ∨ observed+count≤(transitionParams mode l).destination)
    (patches : ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),site.owner+6≤observed ∨ observed+count≤site.owner+2)
    (tape : Listing8LiteralInput.sourceField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.sourceField mode l.input)
    (ruleField : Listing8LiteralInput.scalarField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.scalarField mode l.input)
    (fresh : Listing8LiteralInput.updateStart mode l.input+10≤observed ∨ observed+count≤Listing8LiteralInput.updateStart mode l.input+6)
    (direction : l.direction+10≤observed ∨ observed+count≤l.direction+6) :
    ByteMemory.bytesAt (finish mode l v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [(result mode l v r b reach state entry forward current).2.1,
    DwordMixedImage.bytes_frame _ _ _ _ _ direction,DwordMixedImage.bytes_frame _ _ _ _ _ fresh,
    DwordMixedImage.bytes_frame _ _ _ _ _ ruleField]
  exact Listing8MainRetarget.window mode l v r reach state entry forward current observed count nodeOutside ruleOutside patches tape

theorem instruction_count (mode : Mode) (l : Layout) (v : Values mode) : (program mode l v).length=(if mode=.x86 then 69 else 71) := by
  have owners : (Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l v)).length=19 := by
    cases mode <;> simp [Listing8OwnerSequence.program,Listing8OwnerImage.owners,Listing8OwnerSequence.forms,Listing8CopiedPointer.forms]
  rw [program,List.length_append,Listing8MainRetarget.instruction_count,owners]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8MainLiveOwners
