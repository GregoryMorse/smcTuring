module
public import SmcTuring.Appendix.Listing8ModeOffsets
public import SmcTuring.Appendix.Listing8PrototypeCopy
public import SmcTuring.Appendix.Listing8InputMask

public section
namespace SmcTuring.Appendix.Listing8CopyImage
open Native Listing8Prototypes
abbrev Dword := BitVec 32

structure Layout where
  start : Nat
  sourceNode : Nat
  sourceTransition : Nat
  input : Listing8LiteralInput.Layout
  direction : Nat
structure Values (mode : Mode) where
  tape : Dword
  rule : Dword
  fresh : Dword
  direction : Dword
  back : Word mode
  forward : Word mode
  next : Word mode
  newState : Word mode

@[expose] def secondStart (mode : Mode) (l : Layout) := StringCodec.endpoint mode l.start (nodeSpan mode)
@[expose] def patchStart (mode : Mode) (l : Layout) := StringCodec.endpoint mode (secondStart mode l) (transitionSpan mode)
@[expose] def patchLayout (mode : Mode) (l : Layout) : Listing8ModeOffsets.Layout :=
  { start := patchStart mode l, input := l.input, direction := l.direction }
@[expose] def nodeParams (mode : Mode) (l : Layout) : StringMacroLayout.Params :=
  { start := l.start, source := l.sourceNode, destination := Listing8ModeOffsets.nodeEntry (patchLayout mode l), size := nodeSpan mode }
@[expose] def transitionParams (mode : Mode) (l : Layout) : StringMacroLayout.Params :=
  { start := secondStart mode l, source := l.sourceTransition,
    destination := Listing8ModeOffsets.transitionEntry mode (patchLayout mode l), size := transitionSpan mode }
@[expose] def codeEnd (mode : Mode) (l : Layout) := Listing8ModeOffsets.endPC mode (patchLayout mode l)
@[expose] def sourceNodeBytes (mode : Mode) (l : Layout) (v : Values mode) := nodeBytes mode l.sourceNode v.tape v.back v.forward
@[expose] def sourceTransitionBytes (mode : Mode) (l : Layout) (v : Values mode) :=
  transitionBytes mode l.sourceTransition v.next v.newState v.rule v.fresh v.direction
@[expose] def patchBytes (mode : Mode) (l : Layout) := DwordRetargetSequence.bytes mode (Listing8ModeOffsets.sites mode (patchLayout mode l))
@[expose] def zeroBlock (mode : Mode) (l : Layout) :=
  Listing8ModeOffsets.bytes mode (patchLayout mode l) (Listing8ModeOffsets.nodeEntry (patchLayout mode l))
    (Listing8ModeOffsets.transitionEntry mode (patchLayout mode l)) 0 0 0 0 0 0 0 0
@[expose] def codeBytes (mode : Mode) (l : Layout) :=
  StringMacroLayout.bytes mode (nodeParams mode l) ++ StringMacroLayout.bytes mode (transitionParams mode l) ++ zeroBlock mode l
@[expose] def force : Dword := BitVec.ofNat 32 0x80000000
@[expose] def inputBytes (mode : Mode) (l : Layout) := Listing8InputMask.bytes mode l.input 0 force force force force
@[expose] def image (mode : Mode) (l : Layout) (v : Values mode) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes (ByteMemory.putBytes
    (ByteMemory.putBytes (ByteMemory.putBytes backing l.input.start (inputBytes mode l)) l.start (codeBytes mode l))
    l.sourceNode (sourceNodeBytes mode l v)) l.sourceTransition (sourceTransitionBytes mode l v)
@[expose] def initial (mode : Mode) (l : Layout) (v : Values mode) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  { seed with
    principal := { seed.principal with pc := Arithmetic.encodeNat mode l.start, memory := image mode l v backing }
    backwards := false }

/-- Capacities and separation concern the initial layout only. Neither a
future Ready, copied image nor future trace is part of this contract. -/
structure Resources (mode : Mode) (l : Layout) : Prop where
  node : TemplateCopy.Resources mode (nodeParams mode l)
  transition : TemplateCopy.Resources mode (transitionParams mode l)
  inputAfter : codeEnd mode l ≤ l.input.start
  inputFits : Listing8LiteralInput.endPC mode l.input < 2^(8*mode.wordBytes)
  nodeOutside : l.sourceNode+nodeSpan mode ≤ l.start ∨ Listing8LiteralInput.endPC mode l.input ≤ l.sourceNode
  transitionOutside : l.sourceTransition+transitionSpan mode ≤ l.start ∨ Listing8LiteralInput.endPC mode l.input ≤ l.sourceTransition
  sources : l.sourceNode+nodeSpan mode ≤ l.sourceTransition ∨ l.sourceTransition+transitionSpan mode ≤ l.sourceNode

theorem endpoint_lower (mode : Mode) (start size : Nat) : start ≤ StringCodec.endpoint mode start size := by
  unfold StringCodec.endpoint StringCodec.bodyEnd StringCodec.bodyStart
  omega
theorem coordinates (mode : Mode) (l : Layout) :
    l.start+(StringMacroLayout.bytes mode (nodeParams mode l)).length = secondStart mode l ∧
    secondStart mode l+(StringMacroLayout.bytes mode (transitionParams mode l)).length = patchStart mode l ∧
    patchStart mode l+(zeroBlock mode l).length = codeEnd mode l := by
  have firstLower := endpoint_lower mode l.start (nodeSpan mode)
  have secondLower := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  refine ⟨?_,?_,?_⟩
  · simp only [StringMacroLayout.bytes,nodeParams,StringCodec.whole_length,secondStart]
    omega
  · simp only [StringMacroLayout.bytes,transitionParams,StringCodec.whole_length,patchStart]
    omega
  · exact Listing8ModeOffsets.bytes_length mode (patchLayout mode l) _ _ 0 0 0 0 0 0 0 0
theorem code_length (mode : Mode) (l : Layout) : l.start+(codeBytes mode l).length = codeEnd mode l := by
  have bounds := coordinates mode l
  simp only [codeBytes,List.length_append]
  omega
theorem code_to_input (mode : Mode) (l : Layout) (r : Resources mode l) : codeEnd mode l ≤ Listing8LiteralInput.endPC mode l.input := by
  have endInput := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have afterInput := r.inputAfter
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at endInput <;> omega
theorem byte_frame (memory : ByteMemory.Memory) (address : Nat) (payload : List LittleEndian.Byte) (observed count : Nat)
    (outside : address+payload.length ≤ observed ∨ observed+count ≤ address) :
    ByteMemory.bytesAt (ByteMemory.putBytes memory address payload) observed count = ByteMemory.bytesAt memory observed count := by
  apply ByteMemory.bytes_at_frame
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases outside with before | after <;> omega

theorem initial_code (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode l v backing) l.start (codeBytes mode l).length = codeBytes mode l := by
  have bound := code_length mode l
  have later := code_to_input mode l r
  have nlen : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have tlen : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  have exterior (source size : Nat)
      (outside : source+size ≤ l.start ∨ Listing8LiteralInput.endPC mode l.input ≤ source) :
      source+size ≤ l.start ∨ l.start+(codeBytes mode l).length ≤ source := by
    rcases outside with before | after
    · exact Or.inl before
    · right; omega
  unfold image
  rw [byte_frame _ _ _ _ _ (by rw [tlen]; exact exterior _ _ r.transitionOutside),
    byte_frame _ _ _ _ _ (by rw [nlen]; exact exterior _ _ r.nodeOutside)]
  exact ByteMemory.bytes_at_put _ _ _

theorem initial_source_node (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode l v backing) l.sourceNode (sourceNodeBytes mode l v).length = sourceNodeBytes mode l v := by
  unfold image
  rw [byte_frame _ _ _ _ _]
  · exact ByteMemory.bytes_at_put _ _ _
  · rw [show (sourceNodeBytes mode l v).length = nodeSpan mode from node_length mode _ _ _ _,
      show (sourceTransitionBytes mode l v).length = transitionSpan mode from transition_length mode _ _ _ _ _ _]
    exact Or.symm r.sources
theorem initial_source_transition (mode : Mode) (l : Layout) (v : Values mode) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode l v backing) l.sourceTransition (sourceTransitionBytes mode l v).length = sourceTransitionBytes mode l v :=
  ByteMemory.bytes_at_put _ _ _

theorem initial_node_macro (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode l v backing) l.start (StringMacroLayout.bytes mode (nodeParams mode l)).length =
      StringMacroLayout.bytes mode (nodeParams mode l) := by
  exact ByteWindow.packet _ l.start [] (StringMacroLayout.bytes mode (nodeParams mode l))
    (StringMacroLayout.bytes mode (transitionParams mode l) ++ zeroBlock mode l)
    (by simpa only [codeBytes,List.append_assoc,List.nil_append] using initial_code mode l v r backing)
theorem initial_transition_macro (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode l v backing) (secondStart mode l) (StringMacroLayout.bytes mode (transitionParams mode l)).length =
      StringMacroLayout.bytes mode (transitionParams mode l) := by
  have packet := ByteWindow.packet _ l.start (StringMacroLayout.bytes mode (nodeParams mode l))
    (StringMacroLayout.bytes mode (transitionParams mode l)) (zeroBlock mode l) (initial_code mode l v r backing)
  simpa only [(coordinates mode l).1] using packet
theorem initial_patches (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode l v backing) (patchStart mode l) (patchBytes mode l).length = patchBytes mode l := by
  have packet := ByteWindow.packet _ l.start
    (StringMacroLayout.bytes mode (nodeParams mode l) ++ StringMacroLayout.bytes mode (transitionParams mode l)) (patchBytes mode l)
    (nodeBytes mode (Listing8ModeOffsets.nodeEntry (patchLayout mode l)) 0 0 0 ++
      transitionBytes mode (Listing8ModeOffsets.transitionEntry mode (patchLayout mode l)) 0 0 0 0 0)
    (by simpa only [codeBytes,zeroBlock,Listing8ModeOffsets.bytes,patchBytes,List.append_assoc] using initial_code mode l v r backing)
  simpa only [List.length_append,←Nat.add_assoc,(coordinates mode l).1,(coordinates mode l).2.1] using packet

theorem destinations (mode : Mode) (l : Layout) :
    l.start ≤ (nodeParams mode l).destination ∧
    (nodeParams mode l).destination+nodeSpan mode = (transitionParams mode l).destination ∧
    (transitionParams mode l).destination+transitionSpan mode = codeEnd mode l := by
  have first := endpoint_lower mode l.start (nodeSpan mode)
  have second := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change l.start ≤ secondStart mode l at first
  change secondStart mode l ≤ patchStart mode l at second
  refine ⟨?_,rfl,rfl⟩
  simp only [nodeParams,Listing8ModeOffsets.nodeEntry,patchLayout]
  omega

theorem block_capacity (mode : Mode) (l : Layout) (r : Resources mode l) : codeEnd mode l < 2^(8*mode.wordBytes) := by
  have cap := r.transition.destinationFits
  have size : (transitionParams mode l).size ≤ max (transitionParams mode l).size mode.wordBytes := Nat.le_max_left _ _
  have ending := (destinations mode l).2.2
  change (transitionParams mode l).destination+max (transitionSpan mode) mode.wordBytes < _ at cap
  change transitionSpan mode ≤ max (transitionSpan mode) mode.wordBytes at size
  omega

theorem initial_input (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (backing : ByteMemory.Memory) :
    Listing8InputMask.Intact mode l.input 0 force force force force (image mode l v backing) := by
  have inputLength := Listing8InputMask.bytes_length mode l.input 0 force force force force
  change l.input.start+(inputBytes mode l).length = Listing8LiteralInput.endPC mode l.input at inputLength
  have codeLength := code_length mode l
  have nodeLength : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have transitionLength : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  have begins : l.start ≤ l.input.start := by
    have d := destinations mode l
    have ending := (coordinates mode l).2.2
    have afterInput := r.inputAfter
    omega
  have exterior (source size : Nat)
      (outside : source+size ≤ l.start ∨ Listing8LiteralInput.endPC mode l.input ≤ source) :
      source+size ≤ l.input.start ∨ l.input.start+(inputBytes mode l).length ≤ source := by
    rcases outside with before | after
    · left; omega
    · right; omega
  change ByteMemory.bytesAt (image mode l v backing) l.input.start (inputBytes mode l).length = inputBytes mode l
  unfold image
  rw [byte_frame _ _ _ _ _ (by rw [transitionLength]; exact exterior _ _ r.transitionOutside),
    byte_frame _ _ _ _ _ (by rw [nodeLength]; exact exterior _ _ r.nodeOutside),
    byte_frame _ _ _ _ _ (Or.inl (by rw [codeLength]; exact r.inputAfter))]
  exact ByteMemory.bytes_at_put _ _ _

theorem cursor_end (mode : Mode) (l : Layout) : StringCodec.sourceField mode l.start+mode.wordBytes ≤ patchStart mode l := by
  have field := StringCodec.field_end mode l.start
  have body : StringCodec.bodyStart mode l.start ≤ StringCodec.endpoint mode l.start (nodeSpan mode) := by
    unfold StringCodec.endpoint StringCodec.bodyEnd
    omega
  have second := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l ≤ patchStart mode l at second
  unfold StringCodec.bodyStart at body
  change l.start+2*(StringCodec.initialSize mode+StringCodec.exchangeSize mode) ≤ secondStart mode l at body
  omega

end SmcTuring.Appendix.Listing8CopyImage
