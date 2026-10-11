module
public import SmcTuring.Native.StringPacketRegions
public import SmcTuring.Native.StringMacroEffects
public import SmcTuring.Native.StringMoveWrites
public import SmcTuring.Native.StringRestoreWrites

public section
namespace SmcTuring.Native.StringMacroTemplateWrites
open StringMacroLayout StringMacroEffects StringPacketRegions

/-- Initial bytes derive both native indirect destinations. Only static
ownership of the initializer field and its original referent is supplied. -/
theorem initializer (mode : Mode) (p : Params) (start initial : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start initial)
    (labelOwned : WordAllowed mode p (Arithmetic.encodeNat mode (StringInit.field mode start)))
    (targetOwned : WordAllowed mode p (Arithmetic.encodeNat mode initial)) :
    Run mode p ((StringInit.forms mode start initial).map (StringWrites.liftString mode)) state := by
  have pointer := StringInit.initialized_pointer mode start initial state.principal.memory fits current
  cases mode with
  | x86 => exact ⟨word_packet .x86 p _ (Arithmetic.encodeNat .x86 initial) labelOwned,True.intro⟩
  | x64 =>
    have readerPointer : Execution.load .x64 state.principal.memory (ReaderImage.label .x64 start)=Arithmetic.encodeNat .x64 initial := pointer
    have fields := Reader.four_writes_owned .x64 state.principal (ReaderImage.label .x64 start)
      (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64)
      (ReaderImage.first_hits .x64 start state.principal entry) (ReaderImage.second_hits .x64 start state.principal entry)
      (WordAllowed .x64 p) labelOwned (by rw [readerPointer];exact targetOwned)
    have actual : Writes.OwnedRun .x64 (WordAllowed .x64 p)
        [.memory .exchangeAcc (ReaderImage.firstDisp .x64 start),Reader.storeForm .x64 (ReaderImage.label .x64 start) (ReaderImage.secondDisp .x64),
          .exchangeIndirect,.moffs (Arithmetic.encodeNat .x64 initial)] state.principal := by
      rw [←readerPointer]
      simpa only [Writes.OwnedRun,and_true,Reader.swapped,Reader.restored,Reader.dereferenced] using fields
    have lifted := native_run .x64 p _ state actual
    simpa only [StringInit.forms,StringInit.first_displacement,StringInit.second_displacement,
      ReaderImage.firstDisp,ReaderImage.secondDisp,Reader.storeForm,List.map_cons,List.map_nil,StringWrites.liftNative] using lifted

theorem field_interval (mode : Mode) (p : Params) (field : Nat) (packet : StringWrites.Packet)
    (belongs : field=StringCodec.sourceField mode p.start ∨ field=StringCodec.destinationField mode p.start)
    (lower : field≤packet.address) (upper : packet.address+packet.bytes.length≤field+mode.wordBytes) :
    Allowed mode p packet := by
  rcases belongs with rfl | rfl
  · exact Or.inl ⟨lower,upper⟩
  · exact Or.inr (Or.inl ⟨lower,upper⟩)

theorem exchange (mode : Mode) (p : Params) (destination : Bool) (pc field : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (fieldFits : field<2^(8*mode.wordBytes))
    (belongs : field=StringCodec.sourceField mode p.start ∨ field=StringCodec.destinationField mode p.start) :
    Run mode p [StringWrites.liftString mode (StringOperands.exchange mode destination pc field)] state := by
  have owned := StringFieldWrites.exchange mode destination field (field+mode.wordBytes) pc field state entry range
    (StringFieldWrites.word_owned mode field (field+mode.wordBytes) field fieldFits ⟨Nat.le_refl _,Nat.le_refl _⟩)
  exact interval_run mode p field (field+mode.wordBytes) _ state (field_interval mode p field · belongs) ⟨owned,True.intro⟩

theorem restore (mode : Mode) (p : Params) (destination : Bool) (pc field size : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (exchangeRange : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (subtractRange : mode=.x64 → Relocation.SignedDelta (StringRestore.endpoint mode pc size) field)
    (fieldFits : field<2^(8*mode.wordBytes))
    (belongs : field=StringCodec.sourceField mode p.start ∨ field=StringCodec.destinationField mode p.start) :
    Run mode p ((StringRestore.forms mode destination pc field size).map (StringWrites.liftString mode)) state :=
  interval_run mode p field (field+mode.wordBytes) _ state (field_interval mode p field · belongs)
    (StringRestoreWrites.owned mode destination field (field+mode.wordBytes) pc field size state entry exchangeRange subtractRange
      (StringFieldWrites.word_owned mode field (field+mode.wordBytes) field fieldFits ⟨Nat.le_refl _,Nat.le_refl _⟩))

theorem setup (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    Run mode p ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)) state := by
  have fits := prefix_capacity mode p state ready
  have packets := StringMacroImage.initializer_windows mode p state ready
  have firstFits := (StringSetup.initializer_fits mode p.start fits).1
  have secondFits := (StringSetup.initializer_fits mode p.start fits).2
  have sf := StringSetup.source_field_fits mode p.start fits
  have df := StringSetup.destination_field_fits mode p.start fits
  have source := (source_capacity mode p state ready).2.2
  have destination := (destination_capacity mode p state ready).2.2
  have sourceOwned : WordAllowed mode p (Arithmetic.encodeNat mode p.source) := by
    rw [WordAllowed,Arithmetic.encode_nat_toNat mode _ source];exact Or.inr (Or.inr (Or.inl rfl))
  have destinationOwned : WordAllowed mode p (Arithmetic.encodeNat mode p.destination) := by
    rw [WordAllowed,Arithmetic.encode_nat_toNat mode _ destination];exact Or.inr (Or.inr (Or.inr rfl))
  have sourceField : WordAllowed mode p (Arithmetic.encodeNat mode (StringInit.field mode p.start)) := by
    change WordAllowed mode p (Arithmetic.encodeNat mode (StringCodec.sourceField mode p.start))
    rw [WordAllowed,Arithmetic.encode_nat_toNat mode _ sf];exact Or.inl rfl
  have destinationField : WordAllowed mode p (Arithmetic.encodeNat mode (StringInit.field mode (StringCodec.destinationStart mode p.start))) := by
    change WordAllowed mode p (Arithmetic.encodeNat mode (StringCodec.destinationField mode p.start))
    rw [WordAllowed,Arithmetic.encode_nat_toNat mode _ df];exact Or.inr (Or.inl rfl)
  have first := initializer mode p p.start p.source state ready.entry firstFits packets.1 sourceField sourceOwned
  have initialized := StringInit.effect mode p.start p.source state ready.entry firstFits packets.1
  have firstPC : (StringExecution.run mode (StringInit.forms mode p.start p.source) state).principal.pc=
      Arithmetic.encodeNat mode (p.start+StringCodec.initialSize mode) := by rw [initialized]
  have saveSource := exchange mode p false (p.start+StringCodec.initialSize mode) (StringCodec.sourceField mode p.start)
    (StringExecution.run mode (StringInit.forms mode p.start p.source) state) firstPC (StringSetup.cursor_range mode p.start) sf (Or.inl rfl)
  have sourceRun : Run mode p ((StringSetup.sourceForms mode p.start p.source).map (StringWrites.liftString mode)) state := by
    rw [StringSetup.sourceForms,List.map_append,append,StringWrites.run_lift_string]
    exact ⟨first,saveSource⟩
  let saved := StringExecution.run mode (StringSetup.sourceForms mode p.start p.source) state
  have savedEffect := StringSetup.source_effect mode p.start p.source state ready.entry fits packets.1
  have savedPC : saved.principal.pc=Arithmetic.encodeNat mode (StringCodec.destinationStart mode p.start) := by
    dsimp only [saved];rw [savedEffect]
  have savedCurrent : ByteMemory.bytesAt saved.principal.memory (StringCodec.destinationStart mode p.start) (StringCodec.initialSize mode)=
      StringInit.bytes mode (StringCodec.destinationStart mode p.start) p.destination := by
    dsimp only [saved];rw [savedEffect,StringSetup.destination_window];exact packets.2
  have second := initializer mode p (StringCodec.destinationStart mode p.start) p.destination saved savedPC secondFits savedCurrent destinationField destinationOwned
  have initializedDestination := StringInit.effect mode (StringCodec.destinationStart mode p.start) p.destination saved savedPC secondFits savedCurrent
  have secondPC : (StringExecution.run mode (StringInit.forms mode (StringCodec.destinationStart mode p.start) p.destination) saved).principal.pc=
      Arithmetic.encodeNat mode (StringCodec.destinationStart mode p.start+StringCodec.initialSize mode) := by rw [initializedDestination]
  have saveDestination := exchange mode p true (StringCodec.destinationStart mode p.start+StringCodec.initialSize mode) (StringCodec.destinationField mode p.start)
    (StringExecution.run mode (StringInit.forms mode (StringCodec.destinationStart mode p.start) p.destination) saved)
    secondPC (StringSetup.cursor_range mode (StringCodec.destinationStart mode p.start)) df (Or.inr rfl)
  rw [StringSetup.forms,List.map_append,List.map_append,append,append,StringWrites.run_append]
  simp only [StringWrites.run_lift_string]
  exact ⟨⟨sourceRun,second⟩,saveDestination⟩

theorem moves (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    Run mode p ((StringMoves.forms mode (StringPlan.widths mode p.size)).map (StringWrites.liftString mode))
      (StringMacroEffects.setup mode p state) := by
  have total := StringPlan.total mode p.size
  change (StringPlan.widths mode p.size).sum=p.size at total
  have destination := destination_capacity mode p state ready
  have forward : (StringMacroEffects.setup mode p state).backwards=false := by rw [setup_effect mode p state ready];exact ready.forward
  have di : (StringMacroEffects.setup mode p state).destinationIndex.toNat=p.destination := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ destination.2.2]
  apply interval_run mode p p.destination (p.destination+max p.size mode.wordBytes) _ _
    (fun packet lower upper => Or.inr (Or.inr (Or.inr ⟨lower,upper⟩)))
  apply StringMoveWrites.owned mode _ _ _ _ (StringPlan.positive mode p.size) forward
  · rw [di,total];exact destination.1
  · rw [di,total];exact ⟨Nat.le_refl _,by omega⟩

theorem restores (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    Run mode p ((StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size).map (StringWrites.liftString mode)) (copied mode p state) ∧
    Run mode p ((StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size).map (StringWrites.liftString mode)) (sourceRestored mode p state) := by
  have ranges := tail_ranges mode p ready.sizeFits
  have endPC : StringRestore.endpoint mode (destinationTail mode p) p.size=endpoint mode p := by
    simp only [destinationTail,StringRestore.endpoint,sourceTail,endpoint,StringCodec.endpoint];omega
  exact ⟨restore mode p false _ _ p.size _ (by rw [copied_effect mode p state ready]) (fun _ => ranges.1) (fun _ => ranges.2.1)
      (StringSetup.source_field_fits mode p.start (prefix_capacity mode p state ready)) (Or.inl rfl),
    restore mode p true _ _ p.size _ (by rw [source_effect mode p state ready]) (fun _ => ranges.2.2.1)
      (fun _ => by rw [endPC];exact ranges.2.2.2)
      (StringSetup.destination_field_fits mode p.start (prefix_capacity mode p state ready)) (Or.inr rfl)⟩

/-- Every actual initializer, cursor save, MOVS and restoration packet has
a positively derived complete window in these four static regions. -/
theorem complete (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    Run mode p ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state := by
  have a := setup mode p state ready
  have b := moves mode p state ready
  have c := restores mode p state ready
  simp only [StringProgram.forms,List.map_append,append,StringWrites.run_append,StringWrites.run_lift_string]
  exact ⟨⟨⟨a,b⟩,c.1⟩,c.2⟩

theorem templates (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    StringTemplateStates.Run mode (fun current => StringMacroTemplates.Intact mode p current.principal.memory)
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state :=
  all_states mode p _ state (StringMacroTemplates.initial mode p state.principal.memory ready.initialized)
    ready.sourceOutside ready.destinationOutside (complete mode p state ready)

end SmcTuring.Native.StringMacroTemplateWrites
