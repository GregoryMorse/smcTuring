module
public import SmcTuring.Appendix.Listing8MainCopies
public import SmcTuring.Appendix.Listing8LiveOwnerImage

public section
namespace SmcTuring.Appendix.Listing8MainRetarget
open Native Listing8CopyImage Listing8Prototypes Listing8MainCopyImage
@[expose] def finish (mode : Mode) (l : Layout) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8LiveRetarget.finish mode l v (Listing8MainCopies.finish mode l state)
@[expose] def program (mode : Mode) (l : Layout) (v : Values mode) :=
  (Listing8MainCopies.program mode l).map StringDword.Form.string++Listing8LiveRetarget.program mode l v

theorem retarget_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    StringDword.Trace mode (Listing8MainCopies.finish mode l state) (Listing8LiveRetarget.program mode l v) (finish mode l v state) :=
  Listing8LiveRetarget.trace mode l v r _ (Listing8MainCopies.registers mode l v r state entry forward current).1
    (Listing8MainCopies.retarget_current mode l v r state entry forward current)

theorem trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    StringDword.Trace mode state (program mode l v) (finish mode l v state) :=
  StringDword.trace_append mode (StringDword.string_trace mode (Listing8MainCopies.trace mode l v r state entry forward current))
    (retarget_trace mode l v r state entry forward current)

theorem effect (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    let copied:=Listing8MainCopies.finish mode l state
    finish mode l v state={copied with principal:={copied.principal with
      pc:=Arithmetic.encodeNat mode (backEntry mode (nodeParams mode l).destination)
      memory:=DwordCode.put (DwordRetargetSequence.writes mode (Listing8ModeOffsets.sites mode (patchLayout mode l)) copied.principal.memory)
        (Listing8LiteralInput.sourceField mode l.input) v.tape}} :=
  Listing8LiveRetarget.effect mode l v r reach _ (Listing8MainCopies.registers mode l v r state entry forward current).1

theorem registers (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    (finish mode l v state).principal.pc=Arithmetic.encodeNat mode (backEntry mode (nodeParams mode l).destination) ∧
    (finish mode l v state).principal.stack=state.principal.stack ∧
    (finish mode l v state).sourceIndex=state.sourceIndex ∧
    (finish mode l v state).destinationIndex=state.destinationIndex ∧
    (finish mode l v state).backwards=false ∧ (finish mode l v state).principal.carry=false := by
  have prior:=Listing8MainCopies.registers mode l v r state entry forward current
  rw [effect mode l v r reach state entry forward current]
  exact ⟨rfl,prior.2.1,prior.2.2.1,prior.2.2.2.1,prior.2.2.2.2.1,prior.2.2.2.2.2⟩

/-- Every future copied owner packet and original source operand follows
from the present main-entry contract and the actual copy/retarget writes. -/
theorem owner_current (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    Listing8OwnerSequence.Intact mode (Listing8OwnerImage.owners mode l v) (finish mode l v state).principal.memory := by
  have sources:=Listing8MainCopies.source_packets mode l v r state entry forward current
  exact Listing8LiveOwnerImage.current mode l v r reach _
    (Listing8MainCopies.registers mode l v r state entry forward current).1
    (Listing8MainCopies.retarget_current mode l v r state entry forward current)
    (by simpa only [sourceNodeBytes,node_length] using sources.1)
    (by simpa only [sourceTransitionBytes,transition_length] using sources.2)

theorem window (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) (observed count : Nat)
    (nodeOutside : (nodeParams mode l).destination+nodeSpan mode≤observed ∨ observed+count≤(nodeParams mode l).destination)
    (ruleOutside : (transitionParams mode l).destination+transitionSpan mode≤observed ∨ observed+count≤(transitionParams mode l).destination)
    (patches : ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),site.owner+6≤observed ∨ observed+count≤site.owner+2)
    (tape : Listing8LiteralInput.sourceField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.sourceField mode l.input) :
    ByteMemory.bytesAt (finish mode l v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  change ByteMemory.bytesAt (Listing8LiveRetarget.finish mode l v (Listing8MainCopies.finish mode l state)).principal.memory _ _=_
  rw [Listing8LiveRetarget.frame mode l v r reach _ (Listing8MainCopies.registers mode l v r state entry forward current).1
    observed count patches tape]
  exact Listing8MainCopies.window mode l v r state entry forward current observed count nodeOutside ruleOutside

theorem instruction_count (mode : Mode) (l : Layout) (v : Values mode) : (program mode l v).length=(if mode=.x86 then 50 else 52) := by
  rw [program,List.length_append,List.length_map,Listing8MainCopies.instruction_count,Listing8LiveRetarget.instruction_count]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8MainRetarget
