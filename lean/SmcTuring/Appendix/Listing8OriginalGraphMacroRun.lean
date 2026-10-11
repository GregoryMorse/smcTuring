module
public import SmcTuring.Appendix.Listing8OriginalGraphInitializer

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphMacroRun
open Native StringMacroLayout StringMacroEffects
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Certificate (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,
    (packet.bytes=[] ∨ (packet.address=p.source ∨ packet.address=p.destination) ∧ packet.bytes.length=mode.wordBytes) ∧
    ∀ template∈Listing8OriginalGraphCatalog.catalog mode origin g,Listing8OwnerTemplateCollection.Outside mode template packet →
      Listing8OwnerTemplateCollection.Intact mode template memory ∧ Listing8OwnerTemplateCollection.Decodes mode template memory

theorem empty (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (memory : ByteMemory.Memory)
    (current : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory) : Certificate mode origin g p memory :=
  ⟨⟨0,[]⟩,Or.inl rfl,fun template member _ => ⟨current template member,Listing8OwnerTemplateCollection.decodes mode template memory (current template member)⟩⟩

theorem from_initializer (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (target : Nat) (memory : ByteMemory.Memory)
    (belongs : target=p.source ∨ target=p.destination)
    (current : Listing8OriginalGraphInitializer.Certificate mode origin g target memory) : Certificate mode origin g p memory := by
  obtain ⟨packet,allowed,headers⟩:=current
  refine ⟨packet,?_,headers⟩
  rcases allowed with restored | ⟨address,size⟩
  · exact Or.inl restored
  · exact Or.inr ⟨address ▸ belongs,size⟩

theorem exchange (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params)
    (destination : Bool) (pc field : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (fits : field<2^(8*mode.wordBytes)) (early : field+mode.wordBytes≤Listing8FullTableImage.start mode origin)
    (current : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin g p reached.principal.memory)
      [StringWrites.liftString mode (StringOperands.exchange mode destination pc field)] state := by
  have writes:=StringFieldWrites.exchange mode destination field (field+mode.wordBytes) pc field state entry range
    (StringFieldWrites.word_owned mode field (field+mode.wordBytes) field fits ⟨Nat.le_refl _,Nat.le_refl _⟩)
  have regions:=BoundedStoreRegions.interval mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
    field (field+mode.wordBytes) [StringWrites.liftString mode (StringOperands.exchange mode destination pc field)] state (fun _ _ _ upper => upper.trans early) ⟨writes,True.intro⟩
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached headers => empty mode origin g p reached.principal.memory headers)
    (StringStoreTemplateRuns.preserve mode _ _ _ state current (Listing8OriginalGraphFailureRun.store mode origin g) regions)

theorem setup (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (early : endpoint mode p≤Listing8FullTableImage.start mode origin)
    (current : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin g p reached.principal.memory)
      ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)) state := by
  have fits:=prefix_capacity mode p state ready
  have packets:=StringMacroImage.initializer_windows mode p state ready
  have initialFits:=StringSetup.initializer_fits mode p.start fits
  have coordinates:=field_coordinates mode p
  have bodyEarly : StringCodec.bodyStart mode p.start≤Listing8FullTableImage.start mode origin :=
    (coordinates.2.2.2.1.trans (coordinates.2.2.2.2.1.trans coordinates.2.2.2.2.2)).trans early
  have sourceEarly : StringCodec.sourceField mode p.start+mode.wordBytes≤Listing8FullTableImage.start mode origin := by omega
  have destinationEarly : StringCodec.destinationField mode p.start+mode.wordBytes≤Listing8FullTableImage.start mode origin := by omega
  have firstEnd : p.start+StringCodec.initialSize mode≤Listing8FullTableImage.start mode origin := by
    unfold StringCodec.bodyStart at bodyEarly;omega
  have secondEnd : StringCodec.destinationStart mode p.start+StringCodec.initialSize mode≤Listing8FullTableImage.start mode origin := by
    unfold StringCodec.destinationStart;unfold StringCodec.bodyStart at bodyEarly;omega
  have sf:=StringSetup.source_field_fits mode p.start fits
  have df:=StringSetup.destination_field_fits mode p.start fits
  have first:=StringTemplateStates.monotone mode _ _ _ state
    (fun reached headers => from_initializer mode origin g p p.source reached.principal.memory (Or.inl rfl) headers)
    (Listing8OriginalGraphInitializer.initializer mode origin p.start g p.source state ready.entry initialFits.1 firstEnd
      (source_capacity mode p state ready).2.2 packets.1 current)
  have initialized:=StringInit.effect mode p.start p.source state ready.entry initialFits.1 packets.1
  have firstPC : (StringExecution.run mode (StringInit.forms mode p.start p.source) state).principal.pc=
      Arithmetic.encodeNat mode (p.start+StringCodec.initialSize mode) := by rw [initialized]
  have firstAll : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (StringExecution.run mode (StringInit.forms mode p.start p.source) state).principal.memory := by rw [initialized];exact current
  have saveSource:=exchange mode origin g p false (p.start+StringCodec.initialSize mode) (StringCodec.sourceField mode p.start)
    _ firstPC (StringSetup.cursor_range mode p.start) sf sourceEarly firstAll
  have sourceRun : StringTemplateStates.Run mode (fun reached => Certificate mode origin g p reached.principal.memory)
      ((StringSetup.sourceForms mode p.start p.source).map (StringWrites.liftString mode)) state := by
    rw [StringSetup.sourceForms,List.map_append,StringTemplateStates.append,StringWrites.run_lift_string]
    exact ⟨first,saveSource⟩
  let saved:=StringExecution.run mode (StringSetup.sourceForms mode p.start p.source) state
  have savedEffect:=StringSetup.source_effect mode p.start p.source state ready.entry fits packets.1
  have savedPC : saved.principal.pc=Arithmetic.encodeNat mode (StringCodec.destinationStart mode p.start) := by dsimp only [saved];rw [savedEffect]
  have savedCurrent : ByteMemory.bytesAt saved.principal.memory (StringCodec.destinationStart mode p.start) (StringCodec.initialSize mode)=
      StringInit.bytes mode (StringCodec.destinationStart mode p.start) p.destination := by
    dsimp only [saved];rw [savedEffect,StringSetup.destination_window];exact packets.2
  have savedAll : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) saved.principal.memory := by
    dsimp only [saved];rw [savedEffect]
    exact Listing8OriginalGraphFailureRun.store mode origin g _ _ _ current (by
      rw [LittleEndian.word_encode_length];exact sourceEarly)
  have second:=StringTemplateStates.monotone mode _ _ _ saved
    (fun reached headers => from_initializer mode origin g p p.destination reached.principal.memory (Or.inr rfl) headers)
    (Listing8OriginalGraphInitializer.initializer mode origin (StringCodec.destinationStart mode p.start) g p.destination saved savedPC
      initialFits.2 secondEnd (destination_capacity mode p state ready).2.2 savedCurrent savedAll)
  have initializedDestination:=StringInit.effect mode (StringCodec.destinationStart mode p.start) p.destination saved savedPC initialFits.2 savedCurrent
  have secondPC : (StringExecution.run mode (StringInit.forms mode (StringCodec.destinationStart mode p.start) p.destination) saved).principal.pc=
      Arithmetic.encodeNat mode (StringCodec.destinationStart mode p.start+StringCodec.initialSize mode) := by rw [initializedDestination]
  have secondAll : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (StringExecution.run mode (StringInit.forms mode (StringCodec.destinationStart mode p.start) p.destination) saved).principal.memory := by
    rw [initializedDestination];exact savedAll
  have saveDestination:=exchange mode origin g p true (StringCodec.destinationStart mode p.start+StringCodec.initialSize mode)
    (StringCodec.destinationField mode p.start) _ secondPC (StringSetup.cursor_range mode (StringCodec.destinationStart mode p.start)) df
    destinationEarly secondAll
  rw [StringSetup.forms,List.map_append,List.map_append,StringTemplateStates.append,StringTemplateStates.append,StringWrites.run_append]
  simp only [StringWrites.run_lift_string]
  exact ⟨⟨sourceRun,second⟩,saveDestination⟩

theorem setup_endpoint (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (early : endpoint mode p≤Listing8FullTableImage.start mode origin)
    (current : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (StringMacroEffects.setup mode p state).principal.memory := by
  have coordinates:=field_coordinates mode p
  have bodyEarly : bodyStart mode p≤Listing8FullTableImage.start mode origin :=
    (coordinates.2.2.2.1.trans (coordinates.2.2.2.2.1.trans coordinates.2.2.2.2.2)).trans early
  have sourceEarly : StringCodec.sourceField mode p.start+mode.wordBytes≤Listing8FullTableImage.start mode origin := by omega
  have destinationEarly : StringCodec.destinationField mode p.start+mode.wordBytes≤Listing8FullTableImage.start mode origin := by omega
  rw [setup_effect mode p state ready]
  change Listing8OwnerTemplateCollection.All mode _ (ByteMemory.putWord mode (ByteMemory.putWord mode state.principal.memory
    (StringCodec.sourceField mode p.start) state.sourceIndex) (StringCodec.destinationField mode p.start) state.destinationIndex)
  apply Listing8OriginalGraphFailureRun.store mode origin g
  · exact Listing8OriginalGraphFailureRun.store mode origin g _ _ _ current (by
      rw [LittleEndian.word_encode_length];exact sourceEarly)
  · rw [LittleEndian.word_encode_length];exact destinationEarly

theorem moves (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (early : endpoint mode p≤Listing8FullTableImage.start mode origin)
    (destinationEarly : p.destination+p.size≤Listing8FullTableImage.start mode origin)
    (current : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8OwnerTemplateCollection.All mode
      (Listing8OriginalGraphCatalog.catalog mode origin g) reached.principal.memory)
      ((StringMoves.forms mode (StringPlan.widths mode p.size)).map (StringWrites.liftString mode)) (StringMacroEffects.setup mode p state) := by
  have total:=StringPlan.total mode p.size
  change (StringPlan.widths mode p.size).sum=p.size at total
  have destination:=destination_capacity mode p state ready
  have forward : (StringMacroEffects.setup mode p state).backwards=false := by rw [setup_effect mode p state ready];exact ready.forward
  have di : (StringMacroEffects.setup mode p state).destinationIndex.toNat=p.destination := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ destination.2.2]
  have owned:=StringMoveWrites.owned mode p.destination (p.destination+p.size) (StringPlan.widths mode p.size)
    (StringMacroEffects.setup mode p state) (StringPlan.positive mode p.size) forward
    (by rw [di,total];exact destination.1) (by rw [di,total];exact ⟨Nat.le_refl _,Nat.le_refl _⟩)
  exact StringStoreTemplateRuns.preserve mode (fun address count => address+count≤Listing8FullTableImage.start mode origin) _ _ _
    (setup_endpoint mode origin g p state ready early current) (Listing8OriginalGraphFailureRun.store mode origin g)
    (BoundedStoreRegions.interval mode _ p.destination (p.destination+p.size) _ _ (fun _ _ _ upper => upper.trans destinationEarly) owned)

theorem restores (mode : Mode) (origin : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (early : endpoint mode p≤Listing8FullTableImage.start mode origin) :
    StringStoreRegions.Run mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
      ((StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size).map (StringWrites.liftString mode)) (copied mode p state) ∧
    StringStoreRegions.Run mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
      ((StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size).map (StringWrites.liftString mode)) (sourceRestored mode p state) := by
  have ranges:=tail_ranges mode p ready.sizeFits
  have coordinates:=field_coordinates mode p
  have bodyEarly : bodyStart mode p≤Listing8FullTableImage.start mode origin :=
    (coordinates.2.2.2.1.trans (coordinates.2.2.2.2.1.trans coordinates.2.2.2.2.2)).trans early
  have sourceEarly : StringCodec.sourceField mode p.start+mode.wordBytes≤Listing8FullTableImage.start mode origin := by omega
  have destinationEarly : StringCodec.destinationField mode p.start+mode.wordBytes≤Listing8FullTableImage.start mode origin := by omega
  have endPC : StringRestore.endpoint mode (destinationTail mode p) p.size=endpoint mode p := by
    simp only [destinationTail,StringRestore.endpoint,sourceTail,endpoint,StringCodec.endpoint];omega
  have keep (destination : Bool) (pc field : Nat) (reached : StringExecution.State mode)
      (position : reached.principal.pc=Arithmetic.encodeNat mode pc)
      (exchangeRange : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
      (subtractRange : mode=.x64 → Relocation.SignedDelta (StringRestore.endpoint mode pc p.size) field)
      (fits : field<2^(8*mode.wordBytes)) (before : field+mode.wordBytes≤Listing8FullTableImage.start mode origin) :
      StringStoreRegions.Run mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
        ((StringRestore.forms mode destination pc field p.size).map (StringWrites.liftString mode)) reached := by
    exact BoundedStoreRegions.interval mode _ field (field+mode.wordBytes) _ reached (fun _ _ _ upper => upper.trans before)
      (StringRestoreWrites.owned mode destination field (field+mode.wordBytes) pc field p.size reached position exchangeRange subtractRange
        (StringFieldWrites.word_owned mode field (field+mode.wordBytes) field fits ⟨Nat.le_refl _,Nat.le_refl _⟩))
  exact ⟨keep false _ _ _ (by rw [copied_effect mode p state ready]) (fun _ => ranges.1) (fun _ => ranges.2.1)
      (StringSetup.source_field_fits mode p.start (prefix_capacity mode p state ready)) sourceEarly,
    keep true _ _ _ (by rw [source_effect mode p state ready]) (fun _ => ranges.2.2.1)
      (fun _ => by rw [endPC];exact ranges.2.2.2)
      (StringSetup.destination_field_fits mode p.start (prefix_capacity mode p state ready)) destinationEarly⟩

theorem complete (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (early : endpoint mode p≤Listing8FullTableImage.start mode origin)
    (destinationEarly : p.destination+p.size≤Listing8FullTableImage.start mode origin)
    (current : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin g p reached.principal.memory)
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state := by
  have a:=setup mode origin g p state ready early current
  have b:=moves mode origin g p state ready early destinationEarly current
  have c:=restores mode origin p state ready early
  have copiedAll:=StringTemplateStates.at_prefix mode _ _ [] (StringMacroEffects.setup mode p state)
    (by simpa only [List.append_nil] using b)
  rw [StringWrites.run_lift_string] at copiedAll
  have sourceRun:=StringStoreTemplateRuns.preserve mode _ _ _ _ copiedAll (Listing8OriginalGraphFailureRun.store mode origin g) c.1
  have sourceAll:=StringTemplateStates.at_prefix mode _ _ [] (copied mode p state)
    (by simpa only [List.append_nil,copied] using sourceRun)
  rw [StringWrites.run_lift_string] at sourceAll
  have destinationRun:=StringStoreTemplateRuns.preserve mode _ _ _ _ sourceAll (Listing8OriginalGraphFailureRun.store mode origin g) c.2
  simp only [StringProgram.forms,List.map_append,StringTemplateStates.append,StringWrites.run_append,StringWrites.run_lift_string]
  exact ⟨⟨⟨a,StringTemplateStates.monotone mode _ _ _ _ (fun reached headers => empty mode origin g p reached.principal.memory headers) b⟩,
    StringTemplateStates.monotone mode _ _ _ _ (fun reached headers => empty mode origin g p reached.principal.memory headers) sourceRun⟩,
    StringTemplateStates.monotone mode _ _ _ _ (fun reached headers => empty mode origin g p reached.principal.memory headers) destinationRun⟩

theorem endpoint (mode : Mode) (origin : Nat) (g : Listing8SourceGraph.Graph) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (destinationEarly : p.destination+p.size≤Listing8FullTableImage.start mode origin)
    (current : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (finish mode p state).principal.memory := by
  rw [finish_effect mode p state ready]
  exact Listing8OriginalGraphFailureRun.store mode origin g _ _ _ current (by rw [ByteMemory.bytes_at_length];exact destinationEarly)

end SmcTuring.Appendix.Listing8OriginalGraphMacroRun
