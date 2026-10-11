module
public import SmcTuring.Appendix.Listing8Prototypes
public import SmcTuring.Appendix.Listing8LiteralInput
public import SmcTuring.Native.DwordRetargetSequence

public section
namespace SmcTuring.Appendix.Listing8ModeOffsets
open Native Listing8Prototypes
abbrev Site := DwordRetargetSequence.Site
abbrev Dword := BitVec 32

/-- Four literal MOVEMODEOFFS packets immediately precede the copied node
and transition owners. Destinations name the SUB, M14 MOV, XOR and direction
instruction entries; their live immediate fields are at +6. -/
structure Layout where
  start : Nat
  input : Listing8LiteralInput.Layout
  direction : Nat

@[expose] def nodeEntry (layout : Layout) := layout.start+40
@[expose] def transitionEntry (mode : Mode) (layout : Layout) := nodeEntry layout+nodeSpan mode
@[expose] def endPC (mode : Mode) (layout : Layout) := transitionEntry mode layout+transitionSpan mode
@[expose] def sites (mode : Mode) (layout : Layout) : List Site :=
  [{ pc := layout.start, owner := nodeEntry layout, destination := Listing8LiteralInput.ownerPC mode layout.input+10 },
   { pc := layout.start+10, owner := currentEntry mode (transitionEntry mode layout), destination := Listing8LiteralInput.ownerPC mode layout.input },
   { pc := layout.start+20, owner := newEntry mode (transitionEntry mode layout), destination := Listing8LiteralInput.updateStart mode layout.input },
   { pc := layout.start+30, owner := directionEntry mode (transitionEntry mode layout), destination := layout.direction }]
@[expose] def program (mode : Mode) (layout : Layout) := DwordRetargetSequence.program mode (sites mode layout)
@[expose] def finish (mode : Mode) (layout : Layout) (state : Execution.State mode) :=
  DwordRetargetSequence.finish mode (sites mode layout) state

/-- Source-bound prototype bytes, with their original address fields, are
copied verbatim. The four actual patches replace those old scalar addresses.
Pointer-owner relocation/execution is the later full-prologue obligation. -/
@[expose] def bytes (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) :=
  DwordRetargetSequence.bytes mode (sites mode layout) ++ nodeBytes mode sourceNode tape back forward ++
    transitionBytes mode sourceTransition next state rule fresh direction
@[expose] def image (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes backing layout.start (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state)

theorem geometry (mode : Mode) (layout : Layout) :
    nodeEntry layout = layout.start+40 ∧
    transitionEntry mode layout = layout.start+(if mode = .x86 then 86 else 104) ∧
    endPC mode layout = layout.start+(if mode = .x86 then 152 else 188) := by
  cases mode <;> simp [nodeEntry,transitionEntry,endPC,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,Nat.add_assoc]

theorem sites_length (mode : Mode) (layout : Layout) : (sites mode layout).length = 4 := rfl
theorem chain (mode : Mode) (layout : Layout) : DwordRetargetSequence.Contiguous layout.start (sites mode layout) := by
  simp [sites,DwordRetargetSequence.Contiguous,Nat.add_assoc]
theorem distinct (mode : Mode) (layout : Layout) : (sites mode layout).Nodup := by
  simp [sites,DwordRetargetSequence.Site.mk.injEq]

theorem owners_after_patches (mode : Mode) (layout : Layout) (site : Site) (member : site ∈ sites mode layout) :
    layout.start+40 ≤ site.owner ∧ site.owner+10 ≤ endPC mode layout ∧ site.pc+10 ≤ layout.start+40 := by
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    cases mode <;> simp [nodeEntry,transitionEntry,endPC,currentEntry,newEntry,directionEntry,nodeSpan,
      transitionSpan,pointerSpan,ReaderImage.totalSize]

theorem outside (mode : Mode) (layout : Layout) : DwordRetargetSequence.OutsideCodes (sites mode layout) := by
  intro writer writerMember reader readerMember
  have w := owners_after_patches mode layout writer writerMember
  have r := owners_after_patches mode layout reader readerMember
  right
  omega

theorem owners_separate (mode : Mode) (layout : Layout) (writer reader : Site)
    (writerMember : writer ∈ sites mode layout) (readerMember : reader ∈ sites mode layout) (different : writer ≠ reader) :
    writer.owner+6 ≤ reader.owner ∨ reader.owner+10 ≤ writer.owner+2 := by
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at writerMember readerMember
  rcases writerMember with rfl | rfl | rfl | rfl <;>
    rcases readerMember with rfl | rfl | rfl | rfl
  all_goals try exact False.elim (different rfl)
  all_goals cases mode <;> simp [nodeEntry,transitionEntry,currentEntry,newEntry,directionEntry,
    nodeSpan,pointerSpan,ReaderImage.totalSize]

/-- These four short forward patch reaches follow from the literal layout,
independently of the later operand destinations. -/
theorem patch_ranges (mode : Mode) (layout : Layout) :
    ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2) := by
  intro site member long
  subst mode
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    unfold Relocation.SignedDelta Relocation.delta <;>
    simp [nodeEntry,transitionEntry,currentEntry,newEntry,directionEntry,nodeSpan,pointerSpan,ReaderImage.totalSize] <;> omega

theorem valid (mode : Mode) (layout : Layout) (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2)) :
    ∀ site ∈ sites mode layout, DwordRetargetSequence.Valid mode site := by
  intro site member
  have bounds := owners_after_patches mode layout site member
  have start : layout.start+40 ≤ endPC mode layout := by
    have g := geometry mode layout
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at g <;> omega
  exact ⟨by omega,by omega,ranges site member⟩

theorem bytes_length (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) :
    layout.start+(bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state).length = endPC mode layout := by
  simp only [bytes,List.length_append,DwordRetargetSequence.bytes_length,sites_length,node_length,transition_length]
  unfold endPC transitionEntry nodeEntry
  omega

theorem initial_image (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode layout sourceNode sourceTransition tape rule fresh direction back forward next state backing)
      layout.start (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state := ByteMemory.bytes_at_put _ _ _

theorem initial_patches (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state) :
    DwordRetargetSequence.Intact mode (sites mode layout) memory := by
  apply DwordRetargetSequence.intact_of_bytes mode _ layout.start (chain mode layout)
  exact ByteWindow.packet memory layout.start [] (DwordRetargetSequence.bytes mode (sites mode layout))
    (nodeBytes mode sourceNode tape back forward ++ transitionBytes mode sourceTransition next state rule fresh direction)
    (by simpa [bytes,List.append_assoc] using current)

theorem trace (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : ByteMemory.bytesAt state.memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState) :
    MixedDword.Trace mode state (program mode layout) (finish mode layout state) :=
  DwordRetargetSequence.trace mode _ layout.start (chain mode layout) (valid mode layout capacity ranges) (outside mode layout)
    state entry (initial_patches mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState _ current)

theorem effect (mode : Mode) (layout : Layout) (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    finish mode layout state = { state with
      pc := Arithmetic.encodeNat mode (nodeEntry layout)
      memory := DwordRetargetSequence.writes mode (sites mode layout) state.memory } := by
  simpa only [sites_length,nodeEntry,finish,Nat.reduceMul] using
    DwordRetargetSequence.effect mode _ layout.start (chain mode layout) (valid mode layout capacity ranges) state entry

theorem copied_node (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state) :
    ByteMemory.bytesAt memory (nodeEntry layout) (nodeBytes mode sourceNode tape back forward).length =
      nodeBytes mode sourceNode tape back forward := by
  have packet := ByteWindow.packet memory layout.start (DwordRetargetSequence.bytes mode (sites mode layout))
    (nodeBytes mode sourceNode tape back forward) (transitionBytes mode sourceTransition next state rule fresh direction) current
  simpa only [DwordRetargetSequence.bytes_length,sites_length,Nat.reduceMul,nodeEntry] using packet

theorem copied_transition (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state) :
    ByteMemory.bytesAt memory (transitionEntry mode layout)
      (transitionBytes mode sourceTransition next state rule fresh direction).length =
      transitionBytes mode sourceTransition next state rule fresh direction := by
  have packet := ByteWindow.packet memory layout.start
    (DwordRetargetSequence.bytes mode (sites mode layout) ++ nodeBytes mode sourceNode tape back forward)
    (transitionBytes mode sourceTransition next state rule fresh direction) [] (by simpa [bytes] using current)
  simpa only [List.length_append,DwordRetargetSequence.bytes_length,sites_length,Nat.reduceMul,node_length,
    transitionEntry,nodeEntry,Nat.add_assoc] using packet

theorem source_owners (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next state : Word mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next state) :
    ByteMemory.bytesAt memory (nodeEntry layout) 10 = DwordOwner.bytes mode sourceNode tape ∧
    ByteMemory.bytesAt memory (currentEntry mode (transitionEntry mode layout)) 10 =
      DwordOwner.bytes mode (currentEntry mode sourceTransition) rule ∧
    ByteMemory.bytesAt memory (newEntry mode (transitionEntry mode layout)) 10 =
      DwordOwner.bytes mode (newEntry mode sourceTransition) fresh ∧
    ByteMemory.bytesAt memory (directionEntry mode (transitionEntry mode layout)) 10 =
      DwordOwner.bytes mode (directionEntry mode sourceTransition) direction := by
  have node := copied_node mode layout sourceNode sourceTransition tape rule fresh direction back forward next state memory current
  have transition := copied_transition mode layout sourceNode sourceTransition tape rule fresh direction back forward next state memory current
  have a := ByteWindow.packet memory (nodeEntry layout) [] (DwordOwner.bytes mode sourceNode tape)
    (pointerBytes mode (backEntry mode sourceNode) back ++ pointerBytes mode (forwardEntry mode sourceNode) forward)
    (by simpa [nodeBytes,List.append_assoc] using node)
  have b := ByteWindow.packet memory (transitionEntry mode layout) (pointerBytes mode sourceTransition next)
    (DwordOwner.bytes mode (currentEntry mode sourceTransition) rule)
    (DwordOwner.bytes mode (newEntry mode sourceTransition) fresh ++ DwordOwner.bytes mode (directionEntry mode sourceTransition) direction ++
      pointerBytes mode (stateEntry mode sourceTransition) state)
    (by simpa [transitionBytes,List.append_assoc] using transition)
  have c := ByteWindow.packet memory (transitionEntry mode layout)
    (pointerBytes mode sourceTransition next ++ DwordOwner.bytes mode (currentEntry mode sourceTransition) rule)
    (DwordOwner.bytes mode (newEntry mode sourceTransition) fresh)
    (DwordOwner.bytes mode (directionEntry mode sourceTransition) direction ++ pointerBytes mode (stateEntry mode sourceTransition) state)
    (by simpa [transitionBytes,List.append_assoc] using transition)
  have d := ByteWindow.packet memory (transitionEntry mode layout)
    (pointerBytes mode sourceTransition next ++ DwordOwner.bytes mode (currentEntry mode sourceTransition) rule ++
      DwordOwner.bytes mode (newEntry mode sourceTransition) fresh)
    (DwordOwner.bytes mode (directionEntry mode sourceTransition) direction) (pointerBytes mode (stateEntry mode sourceTransition) state)
    (by simpa [transitionBytes,List.append_assoc] using transition)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [List.length_nil,Nat.add_zero,DwordOwner.length] using a
  · simpa only [pointer_length,DwordOwner.length,currentEntry] using b
  · simpa only [List.length_append,pointer_length,DwordOwner.length,currentEntry,newEntry,Nat.add_assoc] using c
  · simpa only [List.length_append,pointer_length,DwordOwner.length,currentEntry,newEntry,directionEntry,Nat.add_assoc] using d

/-- All four actual patches derive the complete future MOV packets from
the copied source-addressed owners, including headers and live immediates.
No later current packet or future trace is an input premise. -/
theorem retargeted_owners (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : ByteMemory.bytesAt state.memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState) :
    ByteMemory.bytesAt (finish mode layout state).memory (nodeEntry layout) 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (nodeEntry layout) (Listing8LiteralInput.sourceField mode layout.input) tape) ∧
    ByteMemory.bytesAt (finish mode layout state).memory (currentEntry mode (transitionEntry mode layout)) 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (currentEntry mode (transitionEntry mode layout)) (Listing8LiteralInput.scalarField mode layout.input) rule) ∧
    ByteMemory.bytesAt (finish mode layout state).memory (newEntry mode (transitionEntry mode layout)) 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (newEntry mode (transitionEntry mode layout)) (Listing8LiteralInput.updateStart mode layout.input+6) fresh) ∧
    ByteMemory.bytesAt (finish mode layout state).memory (directionEntry mode (transitionEntry mode layout)) 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (directionEntry mode (transitionEntry mode layout)) (layout.direction+6) direction) := by
  have source := source_owners mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState _ current
  rw [effect mode layout capacity ranges state entry]
  have packet (reader : Site) (member : reader ∈ sites mode layout) (oldPC : Nat) (value : Dword)
      (original : ByteMemory.bytesAt state.memory reader.owner 10 = DwordOwner.bytes mode oldPC value) :
      ByteMemory.bytesAt (DwordRetargetSequence.writes mode (sites mode layout) state.memory) reader.owner 10 =
        DwordArithmetic.encode (DwordRetarget.ownerForm mode reader.owner (reader.destination+6) value) :=
    DwordRetargetSequence.owner_current mode _ (distinct mode layout) reader member state.memory
      (DwordOwner.form mode oldPC value).displacement value (by rw [←DwordRetarget.owner_bytes]; exact original)
      (fun writer writerMember different => owners_separate mode layout writer reader writerMember member different)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Listing8LiteralInput.sourceField,Nat.add_assoc] using packet
      { pc := layout.start, owner := nodeEntry layout, destination := Listing8LiteralInput.ownerPC mode layout.input+10 }
      (by simp [sites]) sourceNode tape source.1
  · exact packet
      { pc := layout.start+10, owner := currentEntry mode (transitionEntry mode layout), destination := Listing8LiteralInput.ownerPC mode layout.input }
      (by simp [sites]) (currentEntry mode sourceTransition) rule source.2.1
  · exact packet
      { pc := layout.start+20, owner := newEntry mode (transitionEntry mode layout), destination := Listing8LiteralInput.updateStart mode layout.input }
      (by simp [sites]) (newEntry mode sourceTransition) fresh source.2.2.1
  · exact packet
      { pc := layout.start+30, owner := directionEntry mode (transitionEntry mode layout), destination := layout.direction }
      (by simp [sites]) (directionEntry mode sourceTransition) direction source.2.2.2

@[expose] def tapeForm (mode : Mode) (layout : Layout) (tape : Dword) :=
  DwordRetarget.ownerForm mode (nodeEntry layout) (Listing8LiteralInput.sourceField mode layout.input) tape
@[expose] def tapeState (mode : Mode) (layout : Layout) (tape : Dword) (state : Execution.State mode) :=
  DwordArithmetic.execute mode (tapeForm mode layout tape) (finish mode layout state)

/-- The retargeted tape owner executes immediately after the four patches.
The SUB's live tape operand is produced by that actual fifth instruction. -/
theorem tape_owner_trace (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : ByteMemory.bytesAt state.memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState) :
    MixedDword.Trace mode state (program mode layout ++ [.arithmetic (tapeForm mode layout tape)])
      (tapeState mode layout tape state) := by
  have patches := trace mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState
    capacity ranges state entry current
  have packet := (retargeted_owners mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState
    capacity ranges state entry current).1
  have location : (finish mode layout state).pc = Arithmetic.encodeNat mode (nodeEntry layout) := by
    rw [effect mode layout capacity ranges state entry]
  have ownerFits : nodeEntry layout < 2^(8*mode.wordBytes) := by
    have bounds := geometry mode layout
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at bounds <;> omega
  have last : MixedDword.Trace mode (finish mode layout state) [.arithmetic (tapeForm mode layout tape)]
      (tapeState mode layout tape state) := by
    refine .step ?_ (.nil _)
    rw [location,Arithmetic.encode_nat_toNat mode _ ownerFits]
    exact MixedDword.arithmetic_encoding mode _ _ _ packet
  exact MixedDword.trace_append mode patches last

theorem tape_owner_effect (mode : Mode) (layout : Layout) (tape : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
    (targetRange : mode = .x64 → Relocation.SignedDelta (nodeEntry layout+10) (Listing8LiteralInput.sourceField mode layout.input))
    (targetFits : Listing8LiteralInput.sourceField mode layout.input < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    tapeState mode layout tape state = { state with
      pc := Arithmetic.encodeNat mode (backEntry mode (nodeEntry layout))
      memory := DwordCode.put (DwordRetargetSequence.writes mode (sites mode layout) state.memory)
        (Listing8LiteralInput.sourceField mode layout.input) tape } := by
  have location : (finish mode layout state).pc = Arithmetic.encodeNat mode (nodeEntry layout) := by
    rw [effect mode layout capacity ranges state entry]
  have result := DwordArithmetic.located_effect mode (.store 0 tape) (nodeEntry layout)
    (Listing8LiteralInput.sourceField mode layout.input) (finish mode layout state) rfl location targetRange targetFits
  change tapeState mode layout tape state = _ at result
  rw [effect mode layout capacity ranges state entry] at result
  exact result

theorem tape_operand (mode : Mode) (layout : Layout) (tape : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
    (targetRange : mode = .x64 → Relocation.SignedDelta (nodeEntry layout+10) (Listing8LiteralInput.sourceField mode layout.input))
    (targetFits : Listing8LiteralInput.sourceField mode layout.input < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    DwordCode.get (tapeState mode layout tape state).memory (Listing8LiteralInput.sourceField mode layout.input) = tape := by
  rw [tape_owner_effect mode layout tape capacity ranges targetRange targetFits state entry,DwordCode.get_put]

theorem tape_owner_registers (mode : Mode) (layout : Layout) (tape : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (ranges : ∀ site ∈ sites mode layout, mode = .x64 → Relocation.SignedDelta (site.pc+10) (site.owner+2))
    (targetRange : mode = .x64 → Relocation.SignedDelta (nodeEntry layout+10) (Listing8LiteralInput.sourceField mode layout.input))
    (targetFits : Listing8LiteralInput.sourceField mode layout.input < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    (tapeState mode layout tape state).accumulator = state.accumulator ∧
    (tapeState mode layout tape state).stack = state.stack ∧
    (tapeState mode layout tape state).carry = state.carry := by
  rw [tape_owner_effect mode layout tape capacity ranges targetRange targetFits state entry]
  exact ⟨rfl,rfl,rfl⟩

/-- Original whole source-bound block, all five actual fetches and the live
SUB operand. Patch reaches/separation and future owner packets are derived;
the later tape-to-SUB reach and complete DWORD capacity remain explicit. -/
theorem original_correct (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (targetRange : mode = .x64 → Relocation.SignedDelta (nodeEntry layout+10) (Listing8LiteralInput.sourceField mode layout.input))
    (targetFits : Listing8LiteralInput.sourceField mode layout.input+4 ≤ 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (backing : ByteMemory.Memory)
    (initialized : state.memory = image mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState backing) :
    MixedDword.Trace mode state (program mode layout ++ [.arithmetic (tapeForm mode layout tape)])
      (tapeState mode layout tape state) ∧
    DwordCode.get (tapeState mode layout tape state).memory (Listing8LiteralInput.sourceField mode layout.input) = tape ∧
    (tapeState mode layout tape state).accumulator = state.accumulator ∧
    (tapeState mode layout tape state).stack = state.stack ∧
    (tapeState mode layout tape state).carry = state.carry := by
  have current : ByteMemory.bytesAt state.memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState := by
    rw [initialized]
    exact initial_image mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState backing
  have fits : Listing8LiteralInput.sourceField mode layout.input < 2^(8*mode.wordBytes) := by omega
  exact ⟨tape_owner_trace mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState
      capacity (patch_ranges mode layout) state entry current,
    tape_operand mode layout tape capacity (patch_ranges mode layout) targetRange fits state entry,
    tape_owner_registers mode layout tape capacity (patch_ranges mode layout) targetRange fits state entry⟩

/-- The fifth instruction writes into the later input region, preserving
every complete window of the copied prototype block. -/
theorem tape_block_frame (mode : Mode) (layout : Layout) (tape : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (inputAfter : endPC mode layout ≤ layout.input.start)
    (targetRange : mode = .x64 → Relocation.SignedDelta (nodeEntry layout+10) (Listing8LiteralInput.sourceField mode layout.input))
    (targetFits : Listing8LiteralInput.sourceField mode layout.input < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (observed count : Nat) (within : observed+count ≤ endPC mode layout) :
    ByteMemory.bytesAt (tapeState mode layout tape state).memory observed count =
      ByteMemory.bytesAt (finish mode layout state).memory observed count := by
  rw [tape_owner_effect mode layout tape capacity (patch_ranges mode layout) targetRange targetFits state entry,
    effect mode layout capacity (patch_ranges mode layout) state entry]
  apply ByteMemory.bytes_at_frame
  intro index
  have bound := index.isLt
  have source := (Listing8LiteralInput.positions mode layout.input).2.2.1
  simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at source <;> omega

theorem remaining_owners (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (inputAfter : endPC mode layout ≤ layout.input.start)
    (targetRange : mode = .x64 → Relocation.SignedDelta (nodeEntry layout+10) (Listing8LiteralInput.sourceField mode layout.input))
    (targetFits : Listing8LiteralInput.sourceField mode layout.input < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : ByteMemory.bytesAt state.memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length =
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState) :
    ByteMemory.bytesAt (tapeState mode layout tape state).memory (currentEntry mode (transitionEntry mode layout)) 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (currentEntry mode (transitionEntry mode layout)) (Listing8LiteralInput.scalarField mode layout.input) rule) ∧
    ByteMemory.bytesAt (tapeState mode layout tape state).memory (newEntry mode (transitionEntry mode layout)) 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (newEntry mode (transitionEntry mode layout)) (Listing8LiteralInput.updateStart mode layout.input+6) fresh) ∧
    ByteMemory.bytesAt (tapeState mode layout tape state).memory (directionEntry mode (transitionEntry mode layout)) 10 =
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (directionEntry mode (transitionEntry mode layout)) (layout.direction+6) direction) := by
  have ready := (retargeted_owners mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState
    capacity (patch_ranges mode layout) state entry current).2
  have frame (site : Site) (member : site ∈ sites mode layout) :
      ByteMemory.bytesAt (tapeState mode layout tape state).memory site.owner 10 =
        ByteMemory.bytesAt (finish mode layout state).memory site.owner 10 :=
    tape_block_frame mode layout tape capacity inputAfter targetRange targetFits state entry site.owner 10
      (owners_after_patches mode layout site member).2.1
  refine ⟨?_,?_,?_⟩
  · rw [frame { pc := layout.start+10, owner := currentEntry mode (transitionEntry mode layout), destination := Listing8LiteralInput.ownerPC mode layout.input } (by simp [sites])]
    exact ready.1
  · rw [frame { pc := layout.start+20, owner := newEntry mode (transitionEntry mode layout), destination := Listing8LiteralInput.updateStart mode layout.input } (by simp [sites])]
    exact ready.2.1
  · rw [frame { pc := layout.start+30, owner := directionEntry mode (transitionEntry mode layout), destination := layout.direction } (by simp [sites])]
    exact ready.2.2

/-- Each of the four actual patch stores has a nonempty DWORD footprint
wholly inside an initialized copied owner in the complete prototype block. -/
theorem patch_owned (mode : Mode) (layout : Layout) (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    MixedDword.OwnedRun mode (fun address width => layout.start ≤ address ∧ address+width ≤ endPC mode layout)
      (program mode layout) state := by
  apply DwordRetargetSequence.owned_run mode _ layout.start (chain mode layout)
    (valid mode layout capacity (patch_ranges mode layout))
  · intro site member
    have bounds := owners_after_patches mode layout site member
    constructor <;> omega
  · exact entry

end SmcTuring.Appendix.Listing8ModeOffsets
