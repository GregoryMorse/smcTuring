module
public import SmcTuring.Appendix.Listing8CopyOwnerPrefixes
public import SmcTuring.Native.StringMacroTemplateWrites
public import SmcTuring.Native.BoundedStoreRegions
public import SmcTuring.Native.StringStoreTemplateRuns

public section
namespace SmcTuring.Appendix.Listing8CopyOwnerLifetimes
open Native Listing8OwnerTemplateCollection Listing8CopyTemplateWindows StringMacroLayout StringMacroEffects
set_option maxHeartbeats 2000000

/-- Only headers already copied by the actual byte count enter this inventory. -/
@[expose] def inventory (mode : Mode) (p : Params) (templates : List (Template mode)) (count : Nat) :=
  (templates.filter (fun template => decide (start mode template-p.source+header mode template≤count))).map
    (fun template => relocate mode template (p.destination+(start mode template-p.source)))

@[expose] def Property (mode : Mode) (templates : List (Template mode)) (memory : ByteMemory.Memory) :=
  All mode templates memory ∧ ∀ template∈templates,Decodes mode template memory

theorem property (mode : Mode) (templates : List (Template mode)) (memory : ByteMemory.Memory)
    (intact : All mode templates memory) : Property mode templates memory :=
  ⟨intact,fun template member => decodes mode template memory (intact template member)⟩

theorem store (mode : Mode) (templates : List (Template mode)) (memory : ByteMemory.Memory)
    (intact : All mode templates memory) (packet : StringWrites.Packet)
    (outside : ∀ template∈templates,Outside mode template packet) :
    All mode templates (ByteMemory.putBytes memory packet.address packet.bytes) :=
  fun template member => frame mode template memory (intact template member) packet (outside template member)

theorem regions (mode : Mode) (p : Params) (templates : List (Template mode))
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (intact : All mode templates state.principal.memory)
    (outside : ∀ packet,StringPacketRegions.Allowed mode p packet → ∀ template∈templates,Outside mode template packet)
    (writes : StringPacketRegions.Run mode p forms state) :
    StringTemplateStates.Run mode (fun reached => Property mode templates reached.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact property mode templates _ intact
  | cons form rest ih =>
    refine ⟨property mode templates _ intact,ih _ ?_ writes.2⟩
    rw [StringWrites.execute_memory]
    exact store mode templates _ intact _ (outside _ writes.1)

theorem macro_frame (mode : Mode) (p : Params) (templates : List (Template mode))
    (state : StringExecution.State mode) (ready : Ready mode p state)
    (intact : All mode templates state.principal.memory)
    (outside : ∀ packet,StringPacketRegions.Allowed mode p packet → ∀ template∈templates,Outside mode template packet) :
    StringTemplateStates.Run mode (fun reached => Property mode templates reached.principal.memory)
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state :=
  regions mode p templates _ state intact outside (StringMacroTemplateWrites.complete mode p state ready)

theorem reached_inventory (mode : Mode) (p : Params) (templates : List (Template mode))
    (state : StringExecution.State mode) (ready : Ready mode p state)
    (intact : All mode templates state.principal.memory)
    (bounded : Listing8CopyOwnerPrefixes.Bounded mode p templates)
    (first rest : List Nat) (split : StringPlan.widths mode p.size=first++rest) :
    Property mode (inventory mode p templates first.sum)
      (StringMacroCopyPrefixes.reached mode p state first).principal.memory := by
  apply property
  intro copied member
  unfold inventory at member
  rcases List.mem_map.mp member with ⟨template,chosenMember,rfl⟩
  have selected := List.mem_filter.mp chosenMember
  have complete : start mode template-p.source+header mode template≤first.sum := by simpa using selected.2
  have position := bounded template selected.1
  exact (macro_header mode p state ready first rest split template (intact template selected.1) _ (by omega) complete).1

theorem endpoint_inventory (mode : Mode) (p : Params) (templates : List (Template mode))
    (state : StringExecution.State mode) (ready : Ready mode p state)
    (intact : All mode templates state.principal.memory)
    (bounded : Listing8CopyOwnerPrefixes.Bounded mode p templates) :
    Property mode (inventory mode p templates p.size) (finish mode p state).principal.memory := by
  apply property
  intro copied member
  unfold inventory at member
  rcases List.mem_map.mp member with ⟨template,chosenMember,rfl⟩
  have selected := List.mem_filter.mp chosenMember
  have complete : start mode template-p.source+header mode template≤p.size := by simpa using selected.2
  have position := bounded template selected.1
  rw [finish_effect mode p state ready]
  exact copied_header mode template state.principal.memory state.principal.memory (intact template selected.1)
    p.source p.destination p.size _ (by omega) complete

theorem restore_frame (mode : Mode) (templates : List (Template mode)) (destination : Bool)
    (pc field size : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (exchangeRange : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (subtractRange : mode=.x64 → Relocation.SignedDelta (StringRestore.endpoint mode pc size) field)
    (fits : field<2^(8*mode.wordBytes))
    (intact : All mode templates state.principal.memory)
    (outside : ∀ template∈templates,field+mode.wordBytes≤start mode template) :
    StringTemplateStates.Run mode (fun reached => Property mode templates reached.principal.memory)
      ((StringRestore.forms mode destination pc field size).map (StringWrites.liftString mode)) state := by
  have owned := StringRestoreWrites.owned mode destination field (field+mode.wordBytes) pc field size state entry
    exchangeRange subtractRange (StringFieldWrites.word_owned mode field (field+mode.wordBytes) field fits ⟨le_refl _,le_refl _⟩)
  have writes := BoundedStoreRegions.interval mode (fun address count => address+count≤field+mode.wordBytes)
    field (field+mode.wordBytes) _ state (fun _ _ _ upper => upper) owned
  apply StringTemplateStates.monotone mode _ _ _ _ (fun reached kept => property mode templates _ kept)
  exact StringStoreTemplateRuns.preserve mode _ _ _ state intact (fun memory address bytes kept upper =>
    store mode templates memory kept ⟨address,bytes⟩ (fun template member => Or.inl (upper.trans (outside template member)))) writes


theorem copied_inventory (mode : Mode) (p : Params) (templates : List (Template mode))
    (state : StringExecution.State mode) (ready : Ready mode p state)
    (intact : All mode templates state.principal.memory)
    (bounded : Listing8CopyOwnerPrefixes.Bounded mode p templates) :
    Property mode (inventory mode p templates p.size) (copied mode p state).principal.memory := by
  apply property
  intro observed member
  unfold inventory at member
  rcases List.mem_map.mp member with ⟨template,chosenMember,rfl⟩
  have selected := List.mem_filter.mp chosenMember
  have complete : start mode template-p.source+header mode template≤p.size := by simpa using selected.2
  have position := bounded template selected.1
  rw [copied_effect mode p state ready]
  rw [StringFields.copied_effect mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex
    (fields_separate mode p state ready)]
  exact copied_header mode template state.principal.memory _ (intact template selected.1)
    p.source p.destination p.size _ (by omega) complete

theorem inventory_start (mode : Mode) (p : Params) (templates : List (Template mode)) (count : Nat)
    (template : Template mode) (member : template∈inventory mode p templates count) :
    p.destination≤start mode template := by
  unfold inventory at member
  rcases List.mem_map.mp member with ⟨source,_,rfl⟩
  cases source <;> simp [relocate,start]

/-- Both actual restore helpers preserve all newly born headers, including
inside each exchange/subtract, and derive the second seed from the first trace. -/
theorem restorations (mode : Mode) (p : Params) (templates : List (Template mode))
    (state : StringExecution.State mode) (ready : Ready mode p state)
    (intact : All mode templates state.principal.memory)
    (bounded : Listing8CopyOwnerPrefixes.Bounded mode p templates)
    (afterCode : endpoint mode p≤p.destination) :
    StringTemplateStates.Run mode
      (fun reached => Property mode (inventory mode p templates p.size) reached.principal.memory)
      (((StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size)++
        (StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size)).map
        (StringWrites.liftString mode)) (copied mode p state) := by
  have positions := field_coordinates mode p
  have sourceBefore : StringCodec.sourceField mode p.start+mode.wordBytes≤p.destination := by omega
  have destinationBefore : StringCodec.destinationField mode p.start+mode.wordBytes≤p.destination := by omega
  have ranges := tail_ranges mode p ready.sizeFits
  have seed := (copied_inventory mode p templates state ready intact bounded).1
  have first := restore_frame mode (inventory mode p templates p.size) false (sourceTail mode p)
    (StringCodec.sourceField mode p.start) p.size (copied mode p state)
    (by rw [copied_effect mode p state ready]) (fun _ => ranges.1) (fun _ => ranges.2.1)
    (StringSetup.source_field_fits mode p.start (prefix_capacity mode p state ready)) seed
    (fun template member => sourceBefore.trans (inventory_start mode p templates p.size template member))
  have restored := StringTemplateStates.at_prefix mode _
    ((StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size).map
      (StringWrites.liftString mode)) [] (copied mode p state) (by simpa only [List.append_nil] using first)
  rw [StringWrites.run_lift_string] at restored
  change Property mode (inventory mode p templates p.size) (sourceRestored mode p state).principal.memory at restored
  have endPC : StringRestore.endpoint mode (destinationTail mode p) p.size=endpoint mode p := by
    simp only [destinationTail,StringRestore.endpoint,sourceTail,endpoint,StringCodec.endpoint];omega
  have second := restore_frame mode (inventory mode p templates p.size) true (destinationTail mode p)
    (StringCodec.destinationField mode p.start) p.size (sourceRestored mode p state)
    (by rw [source_effect mode p state ready]) (fun _ => ranges.2.2.1)
    (fun _ => by rw [endPC];exact ranges.2.2.2)
    (StringSetup.destination_field_fits mode p.start (prefix_capacity mode p state ready)) restored.1
    (fun template member => destinationBefore.trans (inventory_start mode p templates p.size template member))
  rw [List.map_append,StringTemplateStates.append,StringWrites.run_lift_string]
  exact ⟨first,second⟩


theorem inventory_full (mode : Mode) (p : Params) (templates : List (Template mode))
    (bounded : Listing8CopyOwnerPrefixes.Bounded mode p templates) :
    inventory mode p templates p.size=templates.map
      (fun template => relocate mode template (p.destination+(start mode template-p.source))) := by
  unfold inventory
  have all : templates.filter (fun template => decide (start mode template-p.source+header mode template≤p.size))=templates := by
    apply List.filter_eq_self.mpr
    intro template member
    have bound := bounded template member
    have head := (header_bounds mode template).1
    simp only [decide_eq_true_eq]
    omega
  rw [all]

theorem inventory_unborn (mode : Mode) (p : Params) (templates : List (Template mode)) :
    inventory mode p templates 0=[] := by
  unfold inventory
  have no : ∀ template : Template mode,decide (start mode template-p.source+header mode template≤0)=false := by
    intro template
    cases template with
    | pointer source pc => cases mode <;> simp [header,ReaderImage.labelOffset]
    | scalar pc d => simp [header]
  have empty : templates.filter (fun template => decide (start mode template-p.source+header mode template≤0))=[] := by
    induction templates with
    | nil => rfl
    | cons template rest ih =>
      rw [List.filter_cons,no template]
      exact ih
  rw [empty,List.map_nil]

end SmcTuring.Appendix.Listing8CopyOwnerLifetimes
