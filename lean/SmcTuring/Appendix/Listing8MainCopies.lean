module
public import SmcTuring.Appendix.Listing8MainCopyImage
public import SmcTuring.Appendix.Listing8LiveRetarget

public section
namespace SmcTuring.Appendix.Listing8MainCopies
open Native Listing8CopyImage Listing8Prototypes Listing8MainCopyImage
@[expose] def finish (mode : Mode) (l : Layout) (state : StringExecution.State mode) := Listing8CopyTrace.both mode l state
@[expose] def program (mode : Mode) (l : Layout) := Listing8CopyTrace.program mode l

theorem trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    StringExecution.Trace mode state (program mode l) (finish mode l state) :=
  Listing8LiveCopies.trace mode l r state entry forward (node_current mode l v _ current) (rule_current mode l v _ current)

theorem effect (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    finish mode l state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (patchStart mode l)
      accumulator:=StringInit.accumulator mode (transitionParams mode l).destination (Listing8CopyTrace.first mode l state)
      carry:=false
      memory:=ByteMemory.putBytes (ByteMemory.putBytes state.principal.memory (nodeParams mode l).destination
        (sourceNodeBytes mode l v)) (transitionParams mode l).destination (sourceTransitionBytes mode l v)}} := by
  have actual:=Listing8LiveCopies.effect mode l r state entry forward (node_current mode l v _ current) (rule_current mode l v _ current)
  rw [current.node,current.rule] at actual
  exact actual

theorem window (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) (observed count : Nat)
    (nodeOutside : (nodeParams mode l).destination+nodeSpan mode≤observed ∨ observed+count≤(nodeParams mode l).destination)
    (ruleOutside : (transitionParams mode l).destination+transitionSpan mode≤observed ∨ observed+count≤(transitionParams mode l).destination) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [effect mode l v r state entry forward current,
    byte_frame _ _ _ _ _ (by simpa only [sourceTransitionBytes,transition_length] using ruleOutside),
    byte_frame _ _ _ _ _ (by simpa only [sourceNodeBytes,node_length] using nodeOutside)]

theorem exterior_window (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) (observed count : Nat)
    (outside : observed+count≤l.start ∨ codeEnd mode l≤observed) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  have d:=destinations mode l
  have first : (nodeParams mode l).destination≤(transitionParams mode l).destination := by omega
  apply window mode l v r state entry forward current observed count
  · rcases outside with early | late <;> omega
  · rcases outside with early | late <;> omega

theorem source_packets (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    ByteMemory.bytesAt (finish mode l state).principal.memory l.sourceNode (nodeSpan mode)=sourceNodeBytes mode l v ∧
    ByteMemory.bytesAt (finish mode l state).principal.memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v := by
  have endInput:=code_to_input mode l r
  have nodeOutside : l.sourceNode+nodeSpan mode≤l.start ∨ codeEnd mode l≤l.sourceNode := by
    rcases r.nodeOutside with early | late
    · exact Or.inl early
    · exact Or.inr (Nat.le_trans endInput late)
  have ruleOutside : l.sourceTransition+transitionSpan mode≤l.start ∨ codeEnd mode l≤l.sourceTransition := by
    rcases r.transitionOutside with early | late
    · exact Or.inl early
    · exact Or.inr (Nat.le_trans endInput late)
  exact ⟨(exterior_window mode l v r state entry forward current _ _ nodeOutside).trans current.node,
    (exterior_window mode l v r state entry forward current _ _ ruleOutside).trans current.rule⟩

theorem copied_packets (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    ByteMemory.bytesAt (finish mode l state).principal.memory (nodeParams mode l).destination (sourceNodeBytes mode l v).length=sourceNodeBytes mode l v ∧
    ByteMemory.bytesAt (finish mode l state).principal.memory (transitionParams mode l).destination (sourceTransitionBytes mode l v).length=sourceTransitionBytes mode l v := by
  rw [effect mode l v r state entry forward current]
  constructor
  · rw [byte_frame _ _ _ _ _ (Or.inr (by
      rw [sourceNodeBytes,node_length]
      exact (destinations mode l).2.1.le))]
    exact ByteMemory.bytes_at_put _ _ _
  · exact ByteMemory.bytes_at_put _ _ _

theorem patches (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    ByteMemory.bytesAt (finish mode l state).principal.memory (patchStart mode l) (patchBytes mode l).length=patchBytes mode l := by
  have length : (patchBytes mode l).length=40 := by
    rw [patchBytes,DwordRetargetSequence.bytes_length,Listing8ModeOffsets.sites_length]
  have positions:=destinations mode l
  have nodeStart : (nodeParams mode l).destination=patchStart mode l+40 := rfl
  have bound : patchStart mode l+(patchBytes mode l).length≤(nodeParams mode l).destination := by rw [length,nodeStart]
  have later : (nodeParams mode l).destination≤(transitionParams mode l).destination := by omega
  rw [window mode l v r state entry forward current _ _ (Or.inr bound) (Or.inr (Nat.le_trans bound later))]
  exact current.patches

/-- The future retarget block is obtained by joining the retained actual
patch packets and the two bytestrings just copied by the actual macros. -/
theorem retarget_current (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    Listing8LiveRetarget.Current mode l v (finish mode l state).principal.memory := by
  have copied:=copied_packets mode l v r state entry forward current
  have length : (patchBytes mode l).length=40 := by
    rw [patchBytes,DwordRetargetSequence.bytes_length,Listing8ModeOffsets.sites_length]
  have pair:=ByteWindow.join _ (patchStart mode l) (patchBytes mode l) (sourceNodeBytes mode l v)
    (patches mode l v r state entry forward current)
    (by simpa only [length,nodeParams,patchLayout,Listing8ModeOffsets.nodeEntry] using copied.1)
  exact ByteWindow.join _ (patchStart mode l) (patchBytes mode l++sourceNodeBytes mode l v) (sourceTransitionBytes mode l v) pair (by
    simpa only [List.length_append,length,sourceNodeBytes,node_length,transitionParams,patchLayout,
      Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.nodeEntry,Nat.add_assoc] using copied.2)

theorem registers (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l v state.principal.memory) :
    (finish mode l state).principal.pc=Arithmetic.encodeNat mode (patchStart mode l) ∧
    (finish mode l state).principal.stack=state.principal.stack ∧
    (finish mode l state).sourceIndex=state.sourceIndex ∧
    (finish mode l state).destinationIndex=state.destinationIndex ∧
    (finish mode l state).backwards=false ∧ (finish mode l state).principal.carry=false := by
  rw [effect mode l v r state entry forward current]
  exact ⟨rfl,rfl,rfl,rfl,forward,rfl⟩

theorem instruction_count (mode : Mode) (l : Layout) : (program mode l).length=(if mode=.x86 then 45 else 47) := by
  cases mode <;> simp [program,Listing8CopyTrace.program,StringProgram.forms,StringSetup.forms,StringSetup.sourceForms,
    StringInit.forms,StringMoves.forms,StringRestore.forms,StringPlan.widths,nodeParams,transitionParams,
    nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize]

end SmcTuring.Appendix.Listing8MainCopies
