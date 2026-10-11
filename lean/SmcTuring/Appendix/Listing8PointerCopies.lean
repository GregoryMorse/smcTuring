module
public import SmcTuring.Appendix.Listing8CopiedOwners
public import SmcTuring.Native.StringDwordSequence

public section
namespace SmcTuring.Appendix.Listing8PointerCopies
open Native Listing8CopyImage Listing8Prototypes

/-- Entries of the later newttapeval, itapebptr and itapefptr packets. -/
structure Targets where
  state : Nat
  back : Nat
  forward : Nat

@[expose] def word (mode : Mode) (l : Layout) : ConversionLayout.Layout :=
  ⟨codeEnd mode l,pointerField mode (transitionParams mode l).destination,
    StringCodec.sourceField mode (secondStart mode l)⟩
@[expose] def halfCount (mode : Mode) : Nat := if mode = .x86 then 1 else 2
@[expose] def groupSpan (mode : Mode) := halfCount mode*DwordLayout.span mode
@[expose] def split (mode : Mode) (start source destination : Nat) : List DwordLayout.Layout :=
  match mode with
  | .x86 => [⟨start,source,destination⟩]
  | .x64 => [⟨start,source,destination⟩,⟨start+DwordLayout.span mode,source+4,destination+10⟩]
@[expose] def dwordStart (mode : Mode) (l : Layout) := ConversionLayout.endPC mode (word mode l)
@[expose] def layouts (mode : Mode) (l : Layout) (t : Targets) :=
  split mode (dwordStart mode l) (pointerField mode (stateEntry mode (transitionParams mode l).destination)) (t.state+6) ++
  split mode (dwordStart mode l+groupSpan mode) (pointerField mode (backEntry mode (nodeParams mode l).destination)) (t.back+6) ++
  split mode (dwordStart mode l+2*groupSpan mode) (pointerField mode (forwardEntry mode (nodeParams mode l).destination)) (t.forward+6)
@[expose] def endPC (mode : Mode) (l : Layout) := dwordStart mode l+3*groupSpan mode
@[expose] def wordBytes (mode : Mode) (l : Layout) :=
  (ConversionLayout.program mode (word mode l)).flatMap (Native.encode mode)
@[expose] def bytes (mode : Mode) (l : Layout) (t : Targets) :=
  wordBytes mode l ++ DwordMixedSequence.bytes mode (layouts mode l t)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) :=
  StringDwordCopy.wordProgram mode (word mode l) ++ StringDwordSequence.program mode (layouts mode l t)
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (state : StringExecution.State mode) :=
  StringDwordSequence.finish mode (layouts mode l t) (StringDwordCopy.wordFinish mode (word mode l) state)

/-- All fields are initial static layout certificates; no future byte
image, fetched form, execution or readiness is supplied here. -/
structure Bounds (mode : Mode) (l : Layout) (t : Targets) : Prop where
  wordValid : ConversionLayout.Admissible mode (word mode l)
  dwordValid : ∀ lay ∈ layouts mode l t, DwordLayout.Admissible mode lay
  targetsAfter : ∀ pc ∈ [t.state,t.back,t.forward], endPC mode l ≤ pc

theorem chain (mode : Mode) (l : Layout) (t : Targets) :
    StringDwordSequence.Contiguous mode (dwordStart mode l) (layouts mode l t) := by
  cases mode <;> simp [layouts,split,DwordMixedSequence.Contiguous,groupSpan,halfCount,
    DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.storeSize,DwordLayout.span,Nat.add_assoc]

theorem sizes (mode : Mode) (l : Layout) (t : Targets) :
    (layouts mode l t).length = 3*halfCount mode ∧
    endPC mode l = codeEnd mode l+(if mode = .x86 then 68 else 129) ∧
    (program mode l t).length = if mode = .x86 then 12 else 21 := by
  cases mode <;> simp [layouts,split,halfCount,endPC,dwordStart,word,groupSpan,
    ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC,
    ConversionLayout.exchangeSize,ConversionLayout.storeSize,DwordLayout.span,DwordLayout.storeSize,
    Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,program,
    StringDwordCopy.wordProgram,ConversionLayout.program,StringDwordSequence.program,
    StringDwordCopy.dwordProgram,DwordLayout.program,Nat.add_assoc]

theorem cursor_before_patch (mode : Mode) (l : Layout) :
    (word mode l).destination+mode.wordBytes ≤ patchStart mode l := by
  have field := StringCodec.field_end mode (secondStart mode l)
  have body : StringCodec.bodyStart mode (secondStart mode l) ≤ patchStart mode l := by
    unfold patchStart StringCodec.endpoint StringCodec.bodyEnd;omega
  simp only [word]
  unfold StringCodec.bodyStart at body
  omega

theorem cursor_before (mode : Mode) (l : Layout) :
    (word mode l).destination+mode.wordBytes ≤ codeEnd mode l := by
  have prior := cursor_before_patch mode l
  have ending := (coordinates mode l).2.2
  omega

theorem source_bounds (mode : Mode) (l : Layout) (t : Targets) (lay : DwordLayout.Layout)
    (member : lay ∈ layouts mode l t) :
    patchStart mode l ≤ lay.source ∧ lay.source+4 ≤ codeEnd mode l := by
  cases mode with
  | x86 =>
    simp only [layouts,split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    rcases member with rfl | rfl | rfl <;>
      simp [pointerField,stateEntry,directionEntry,newEntry,currentEntry,backEntry,forwardEntry,
        nodeParams,transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,
        Listing8ModeOffsets.transitionEntry,codeEnd,Listing8ModeOffsets.endPC,nodeSpan,
        transitionSpan,pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset] <;> omega
  | x64 =>
    simp only [layouts,split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [pointerField,stateEntry,directionEntry,newEntry,currentEntry,backEntry,forwardEntry,
        nodeParams,transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,
        Listing8ModeOffsets.transitionEntry,codeEnd,Listing8ModeOffsets.endPC,nodeSpan,
        transitionSpan,pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset] <;> omega

theorem destination_after (mode : Mode) (l : Layout) (t : Targets) (b : Bounds mode l t)
    (lay : DwordLayout.Layout) (member : lay ∈ layouts mode l t) : endPC mode l ≤ lay.destination := by
  have a := b.targetsAfter t.state (by simp)
  have c := b.targetsAfter t.back (by simp)
  have d := b.targetsAfter t.forward (by simp)
  cases mode with
  | x86 =>
    simp only [layouts,split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    rcases member with rfl | rfl | rfl <;>
      simp <;> omega
  | x64 =>
    simp only [layouts,split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp <;> omega

theorem outside (mode : Mode) (l : Layout) (t : Targets) (b : Bounds mode l t) :
    StringDwordSequence.OutsideCodes mode (layouts mode l t) ∧
    StringDwordSequence.SourcesOutside (layouts mode l t) := by
  have codeUpper (lay : DwordLayout.Layout) (member : lay ∈ layouts mode l t) :
      DwordLayout.endPC mode lay ≤ endPC mode l := by
    cases mode with
    | x86 =>
      simp only [layouts,split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
      rcases member with rfl | rfl | rfl <;>
        simp [endPC,groupSpan,halfCount,DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,
          DwordLayout.storeSize,DwordLayout.span]
    | x64 =>
      simp only [layouts,split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [endPC,groupSpan,halfCount,DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,
          DwordLayout.storeSize,DwordLayout.span]
  have beginEnd : codeEnd mode l ≤ endPC mode l := by have geometry := (sizes mode l t).2.1;omega
  constructor
  · intro writer wm reader rm
    right
    have a := destination_after mode l t b writer wm
    have c := codeUpper reader rm;omega
  · intro writer wm reader rm
    right
    have a := destination_after mode l t b writer wm
    have c := source_bounds mode l t reader rm;omega

theorem word_length (mode : Mode) (l : Layout) :
    (wordBytes mode l).length = ConversionLayout.span mode := by
  cases mode <;> rfl

theorem bytes_length (mode : Mode) (l : Layout) (t : Targets) :
    codeEnd mode l+(bytes mode l t).length = endPC mode l := by
  cases mode <;> simp [bytes,word_length,DwordMixedSequence.bytes,layouts,split,
    DwordMixedImage.bytes_length,endPC,dwordStart,ConversionLayout.endpoint,word,
    groupSpan,halfCount,DwordLayout.span,DwordLayout.storeSize,ConversionLayout.span,
    ConversionLayout.exchangeSize,ConversionLayout.storeSize,Native.instructionLength,
    MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Nat.add_assoc]

theorem word_intact (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory (codeEnd mode l) (wordBytes mode l).length = wordBytes mode l) :
    ControlImage.Intact mode (ConversionLayout.entries mode (word mode l)) memory := by
  let lay := word mode l
  have a := ByteWindow.packet memory lay.start [] (Native.encode mode (ConversionLayout.first mode lay))
    (Native.encode mode (ConversionLayout.second mode lay) ++ Native.encode mode (ConversionLayout.third mode lay))
    (by simpa [wordBytes,ConversionLayout.program,List.append_assoc,lay,word] using current)
  have c := ByteWindow.packet memory lay.start (Native.encode mode (ConversionLayout.first mode lay))
    (Native.encode mode (ConversionLayout.second mode lay)) (Native.encode mode (ConversionLayout.third mode lay))
    (by simpa [wordBytes,ConversionLayout.program,List.append_assoc,lay,word] using current)
  have d := ByteWindow.packet memory lay.start
    (Native.encode mode (ConversionLayout.first mode lay) ++ Native.encode mode (ConversionLayout.second mode lay))
    (Native.encode mode (ConversionLayout.third mode lay)) []
    (by simpa [wordBytes,ConversionLayout.program,List.append_assoc,lay,word] using current)
  intro packet member
  change List.Mem packet [⟨lay.start,.fixed (ConversionLayout.first mode lay)⟩,
    ⟨ConversionLayout.secondPC mode lay,.fixed (ConversionLayout.second mode lay)⟩,
    ⟨ConversionLayout.thirdPC mode lay,.fixed (ConversionLayout.third mode lay)⟩] at member
  cases member with
  | head => exact a
  | tail _ rest =>
    cases rest with
    | head =>
      simpa only [ControlImage.PacketIntact,ControlImage.Entry.bytes,ControlImage.Packet.bytes,Native.instruction_length,(ConversionLayout.lengths mode lay).1,ConversionLayout.secondPC] using c
    | tail _ last =>
      cases last with
      | head =>
        simpa only [ControlImage.PacketIntact,ControlImage.Entry.bytes,ControlImage.Packet.bytes,List.length_append,Native.instruction_length,(ConversionLayout.lengths mode lay).1,
          (ConversionLayout.lengths mode lay).2.1,ConversionLayout.thirdPC,ConversionLayout.secondPC,Nat.add_assoc] using d
      | tail _ empty => cases empty

theorem trace (mode : Mode) (l : Layout) (t : Targets) (b : Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l))
    (current : ByteMemory.bytesAt state.principal.memory (codeEnd mode l) (bytes mode l t).length = bytes mode l t) :
    StringDword.Trace mode state (program mode l t) (finish mode l t state) := by
  have firstBytes := ByteWindow.packet state.principal.memory (codeEnd mode l) [] (wordBytes mode l)
    (DwordMixedSequence.bytes mode (layouts mode l t)) current
  have restBytes := ByteWindow.packet state.principal.memory (codeEnd mode l) (wordBytes mode l)
    (DwordMixedSequence.bytes mode (layouts mode l t)) [] (by simpa [bytes,List.append_assoc] using current)
  have position : codeEnd mode l+(wordBytes mode l).length = dwordStart mode l := by
    rw [word_length,dwordStart,ConversionLayout.endpoint];rfl
  rw [position] at restBytes
  let next := StringDwordCopy.wordFinish mode (word mode l) state
  have effect := ConversionEffects.effect mode (word mode l) b.wordValid state.principal entry
  have nextEntry : next.principal.pc = Arithmetic.encodeNat mode (dwordStart mode l) := by
    change (ConversionEffects.finish mode (word mode l) state.principal).pc = _;rw [effect];rfl
  have kept : ByteMemory.bytesAt next.principal.memory (dwordStart mode l)
      (DwordMixedSequence.bytes mode (layouts mode l t)).length = DwordMixedSequence.bytes mode (layouts mode l t) := by
    change ByteMemory.bytesAt (ConversionEffects.finish mode (word mode l) state.principal).memory _ _ = _
    rw [effect]
    unfold ByteMemory.putWord
    rw [byte_frame _ _ _ _ _]
    · exact restBytes
    · left
      rw [LittleEndian.word_encode_length]
      have prior := cursor_before mode l
      have later := ConversionLayout.endpoint mode (word mode l)
      change dwordStart mode l = codeEnd mode l+ConversionLayout.span mode at later
      omega
  exact StringDword.trace_append mode
    (StringDwordCopy.word_trace mode (word mode l) b.wordValid state entry
      (word_intact mode l state.principal.memory (by simpa using firstBytes)))
    (StringDwordSequence.trace mode (layouts mode l t) _ (chain mode l t) b.dwordValid (outside mode l t b).1
      next nextEntry (DwordMixedSequence.intact_of_bytes mode _ _ (chain mode l t) _ kept))

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (b : Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l)) :
    (finish mode l t state).principal.pc = Arithmetic.encodeNat mode (endPC mode l) := by
  have effect := ConversionEffects.effect mode (word mode l) b.wordValid state.principal entry
  have next : (StringDwordCopy.wordFinish mode (word mode l) state).principal.pc =
      Arithmetic.encodeNat mode (dwordStart mode l) := by
    change (ConversionEffects.finish mode (word mode l) state.principal).pc = _;rw [effect];rfl
  have result := StringDwordSequence.endpoint mode (layouts mode l t) _ (chain mode l t) b.dwordValid _ next
  rw [(sizes mode l t).1] at result
  simpa only [finish,endPC,groupSpan,Nat.mul_assoc] using result

theorem memory_effect (mode : Mode) (l : Layout) (t : Targets) (b : Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l)) :
    (finish mode l t state).principal.memory =
      StringDwordSequence.writes state.principal.memory (layouts mode l t)
        (ByteMemory.putWord mode state.principal.memory (word mode l).destination
          (MixedMemory.getWord mode state.principal.memory (word mode l).source)) := by
  have effect := ConversionEffects.effect mode (word mode l) b.wordValid state.principal entry
  let next := StringDwordCopy.wordFinish mode (word mode l) state
  have nextEntry : next.principal.pc = Arithmetic.encodeNat mode (dwordStart mode l) := by
    change (ConversionEffects.finish mode (word mode l) state.principal).pc = _;rw [effect];rfl
  have values : ∀ lay ∈ layouts mode l t,
      DwordCode.get next.principal.memory lay.source = DwordCode.get state.principal.memory lay.source := by
    intro lay member
    change DwordCode.get (ConversionEffects.finish mode (word mode l) state.principal).memory _ = _
    rw [effect]
    apply MixedMemory.dword_after_wide
    intro index
    have bound := index.isLt
    have prior := cursor_before_patch mode l
    have lower := (source_bounds mode l t lay member).1
    unfold ByteMemory.Inside;omega
  have result := StringDwordSequence.memory_snapshot mode (layouts mode l t) _ (chain mode l t)
    b.dwordValid (outside mode l t b).2 state.principal.memory next nextEntry values
  change (finish mode l t state).principal.memory = _ at result
  rw [result]
  change StringDwordSequence.writes _ _ (ConversionEffects.finish mode (word mode l) state.principal).memory = _
  rw [effect,MixedMemory.load_nat]
  have fits := b.wordValid.sourceFits
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  omega

theorem window_frame (mode : Mode) (l : Layout) (t : Targets) (b : Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l))
    (observed count : Nat)
    (wideOutside : (word mode l).destination+mode.wordBytes ≤ observed ∨ observed+count ≤ (word mode l).destination)
    (dwordOutside : ∀ lay ∈ layouts mode l t, lay.destination+4 ≤ observed ∨ observed+count ≤ lay.destination) :
    ByteMemory.bytesAt (finish mode l t state).principal.memory observed count =
      ByteMemory.bytesAt state.principal.memory observed count := by
  rw [memory_effect mode l t b state entry,StringDwordSequence.writes_window _ _ _ _ _ dwordOutside]
  unfold ByteMemory.putWord
  exact byte_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using wideOutside)

theorem registers (mode : Mode) (l : Layout) (t : Targets) (b : Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l)) :
    (finish mode l t state).principal.stack = state.principal.stack ∧
    (finish mode l t state).principal.carry = state.principal.carry ∧
    (finish mode l t state).principal.accumulator = DwordCode.lift mode (DwordCode.low mode state.principal.accumulator) ∧
    (finish mode l t state).sourceIndex = state.sourceIndex ∧
    (finish mode l t state).destinationIndex = state.destinationIndex ∧
    (finish mode l t state).backwards = state.backwards := by
  have effect := ConversionEffects.effect mode (word mode l) b.wordValid state.principal entry
  have nextEntry : (StringDwordCopy.wordFinish mode (word mode l) state).principal.pc =
      Arithmetic.encodeNat mode (dwordStart mode l) := by
    change (ConversionEffects.finish mode (word mode l) state.principal).pc = _;rw [effect];rfl
  have result := StringDwordSequence.registers mode (layouts mode l t) _ (chain mode l t) b.dwordValid _ nextEntry
  have nonempty : (layouts mode l t).length ≠ 0 := by rw [(sizes mode l t).1];cases mode <;> decide
  simpa only [finish,ite_eq_right nonempty,StringDwordCopy.wordFinish,effect] using result

end SmcTuring.Appendix.Listing8PointerCopies
