module
public import SmcTuring.Appendix.Listing8CopyOwnerLifetimes
public import SmcTuring.Appendix.Listing8JointLocalMain

public section
namespace SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun
open Native Listing8CopyImage Listing8Prototypes Listing8CopyOwnerPrefixes Listing8CopyOwnerLifetimes
open Listing8OwnerTemplateCollection StringMacroLayout StringMacroEffects
set_option maxHeartbeats 2000000

/-- The full first inventory ends at the second destination, not inside it. -/
theorem inventory_bounds (mode : Mode) (p : Params) (templates : List (Template mode)) (count : Nat)
    (bounded : Bounded mode p templates) (template : Template mode)
    (member : template∈inventory mode p templates count) :
    p.destination≤start mode template ∧ start mode template+span mode template≤p.destination+p.size := by
  unfold inventory at member
  rcases List.mem_map.mp member with ⟨source,selected,rfl⟩
  have bound := bounded source (List.mem_filter.mp selected).1
  cases source <;> simp only [Listing8CopyTemplateWindows.relocate,start,span] at bound ⊢ <;> omega

/-- All second macro packets avoid every completed first-copy template,
including source/destination initializer exchanges and both restorations. -/
theorem second_outside (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (packet : StringWrites.Packet) (allowed : StringPacketRegions.Allowed mode (transitionParams mode l) packet) :
    ∀ template∈inventory mode (nodeParams mode l) (nodeTemplates mode l v) (nodeSpan mode),
      Outside mode template packet := by
  intro template member
  have bound := inventory_bounds mode (nodeParams mode l) _ _ (node_bounded mode l v) template member
  change (nodeParams mode l).destination≤start mode template ∧
    start mode template+span mode template≤(nodeParams mode l).destination+nodeSpan mode at bound
  have dest := destinations mode l
  have field := field_coordinates mode (transitionParams mode l)
  have early : endpoint mode (transitionParams mode l)≤(nodeParams mode l).destination := by
    change patchStart mode l≤patchStart mode l+40
    omega
  have afterInput := r.inputAfter
  have inputEnd := code_to_input mode l r
  have width : mode.wordBytes≤transitionSpan mode := by cases mode <;> decide
  have size : max (transitionParams mode l).size mode.wordBytes=transitionSpan mode := by
    change max (transitionSpan mode) mode.wordBytes=transitionSpan mode
    exact max_eq_left width
  rcases allowed with sourceField | destinationField | source | destination
  · left
    have upper := sourceField.2
    have body := field.2.2.1
    omega
  · left
    have upper := destinationField.2
    have body := field.2.2.1
    omega
  · rw [size] at source
    rcases r.transitionOutside with first | last
    · left
      have upper := source.2
      change l.sourceTransition≤packet.address ∧ packet.address+packet.bytes.length≤l.sourceTransition+transitionSpan mode at source
      omega
    · right
      change l.sourceTransition≤packet.address ∧ packet.address+packet.bytes.length≤l.sourceTransition+transitionSpan mode at source
      have lower := source.1
      omega
  · right
    rw [size] at destination
    have lower := destination.1
    omega

theorem node_restorations (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode
      (fun reached => Property mode (inventory mode (nodeParams mode l) (nodeTemplates mode l v) (nodeSpan mode)) reached.principal.memory)
      (((StringRestore.forms mode false (sourceTail mode (nodeParams mode l)) (StringCodec.sourceField mode l.start) (nodeSpan mode))++
        (StringRestore.forms mode true (destinationTail mode (nodeParams mode l)) (StringCodec.destinationField mode l.start) (nodeSpan mode))).map
        (StringWrites.liftString mode)) (copied mode (nodeParams mode l) state) := by
  have ready := Listing8LiveCopies.first_ready mode l r state entry forward (Listing8MainCopyImage.node_current mode l v _ current)
  apply restorations mode (nodeParams mode l) (nodeTemplates mode l v) state ready (node_current mode l v _ current.node) (node_bounded mode l v)
  change secondStart mode l≤patchStart mode l+40
  have next := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at next
  omega

theorem node_second_macro (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode
      (fun reached => Property mode (inventory mode (nodeParams mode l) (nodeTemplates mode l v) (nodeSpan mode)) reached.principal.memory)
      ((StringProgram.forms mode (secondStart mode l) l.sourceTransition (transitionParams mode l).destination (transitionSpan mode)).map
        (StringWrites.liftString mode)) (Listing8CopyTrace.first mode l state) := by
  have ready := Listing8LiveCopies.first_ready mode l r state entry forward (Listing8MainCopyImage.node_current mode l v _ current)
  have next := Listing8LiveCopies.second_ready mode l r state ready (Listing8MainCopyImage.rule_current mode l v _ current)
  exact macro_frame mode (transitionParams mode l) _ _ next
    (endpoint_inventory mode (nodeParams mode l) _ state ready (node_current mode l v _ current.node) (node_bounded mode l v)).1
    (second_outside mode l v r)

theorem rule_restorations (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode
      (fun reached => Property mode (inventory mode (transitionParams mode l) (transitionTemplates mode l v) (transitionSpan mode)) reached.principal.memory)
      (((StringRestore.forms mode false (sourceTail mode (transitionParams mode l)) (StringCodec.sourceField mode (secondStart mode l)) (transitionSpan mode))++
        (StringRestore.forms mode true (destinationTail mode (transitionParams mode l)) (StringCodec.destinationField mode (secondStart mode l)) (transitionSpan mode))).map
        (StringWrites.liftString mode)) (copied mode (transitionParams mode l) (Listing8CopyTrace.first mode l state)) := by
  have ready := Listing8LiveCopies.first_ready mode l r state entry forward (Listing8MainCopyImage.node_current mode l v _ current)
  have next := Listing8LiveCopies.second_ready mode l r state ready (Listing8MainCopyImage.rule_current mode l v _ current)
  have source := transition_source_after_first mode l v r state entry forward current
  apply restorations mode (transitionParams mode l) _ _ next (transition_current mode l v _ source) (transition_bounded mode l v)
  change patchStart mode l≤patchStart mode l+40+nodeSpan mode
  omega


@[expose] def patches (mode : Mode) (l : Layout) :=
  (Listing8ModeOffsets.sites mode (patchLayout mode l)).map (fun site => DwordTemplateCollection.Template.binary .store site.pc)

theorem patch_bounds (mode : Mode) (l : Layout) (template : DwordTemplateCollection.Template)
    (member : template∈patches mode l) :
    patchStart mode l≤DwordTemplateCollection.start template ∧
      DwordTemplateCollection.start template+DwordTemplateCollection.span template≤(nodeParams mode l).destination := by
  rcases List.mem_map.mp member with ⟨site,siteMember,rfl⟩
  simp only [Listing8ModeOffsets.sites,List.mem_cons,List.not_mem_nil,or_false] at siteMember
  rcases siteMember with rfl | rfl | rfl | rfl <;>
    simp only [DwordTemplateCollection.start,DwordTemplateCollection.span,patchLayout,nodeParams,Listing8ModeOffsets.nodeEntry] <;> omega

theorem patches_initial (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory)
    (current : Listing8MainCopyImage.Current mode l v memory) : DwordTemplateCollection.All (patches mode l) memory := by
  have actual := DwordRetargetSequence.intact_of_bytes mode (Listing8ModeOffsets.sites mode (patchLayout mode l))
    (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l)) memory current.patches
  intro template member
  rcases List.mem_map.mp member with ⟨site,siteMember,rfl⟩
  exact DwordOperandTemplates.initial .store site.pc _ (DwordRetarget.printed mode site.pc site.owner site.destination)
    memory (actual site siteMember)

theorem patch_packet (mode : Mode) (l : Layout) (p : Params) (packet : StringWrites.Packet)
    (early : endpoint mode p≤patchStart mode l)
    (source : p.source+max p.size mode.wordBytes≤l.start ∨ codeEnd mode l≤p.source)
    (destination : (nodeParams mode l).destination≤p.destination)
    (allowed : StringPacketRegions.Allowed mode p packet) :
    DwordTemplateCollection.CompatibleAll (patches mode l) packet.address packet.bytes.length := by
  intro template member
  have bound := patch_bounds mode l template member
  have fields := field_coordinates mode p
  have start := (destinations mode l).1
  have lower : l.start≤patchStart mode l := by
    have first := endpoint_lower mode l.start (nodeSpan mode)
    have second := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
    change l.start≤secondStart mode l at first
    change secondStart mode l≤patchStart mode l at second
    omega
  have endNode : (nodeParams mode l).destination≤codeEnd mode l := by
    have d := destinations mode l
    omega
  right
  rcases allowed with a | b | c | d
  · left;have upper := a.2;omega
  · left;have upper := b.2;omega
  · rcases source with first | last
    · left;have upper := c.2;omega
    · right;have lower := c.1;omega
  · right;have lower := d.1;omega

theorem patch_macro (mode : Mode) (l : Layout) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (intact : DwordTemplateCollection.All (patches mode l) state.principal.memory)
    (early : endpoint mode p≤patchStart mode l)
    (source : p.source+max p.size mode.wordBytes≤l.start ∨ codeEnd mode l≤p.source)
    (destination : (nodeParams mode l).destination≤p.destination) :
    StringTemplateStates.Run mode (fun reached => DwordTemplateCollection.All (patches mode l) reached.principal.memory)
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state := by
  have actual := StringMacroTemplateWrites.complete mode p state ready
  have regions : StringStoreRegions.Run mode (DwordTemplateCollection.CompatibleAll (patches mode l))
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state := by
    clear ready intact
    generalize (StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)=forms at actual ⊢
    induction forms generalizing state with
    | nil => trivial
    | cons form rest ih => exact ⟨patch_packet mode l p _ early source destination actual.1,ih _ actual.2⟩
  exact StringStoreRegions.arithmetic_states mode _ _ state intact regions

theorem patches_copies (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => DwordTemplateCollection.All (patches mode l) reached.principal.memory)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have firstReady := Listing8LiveCopies.first_ready mode l r state entry forward (Listing8MainCopyImage.node_current mode l v _ current)
  have secondReady := Listing8LiveCopies.second_ready mode l r state firstReady (Listing8MainCopyImage.rule_current mode l v _ current)
  have dest := destinations mode l
  have endInput := code_to_input mode l r
  have firstEnd : endpoint mode (nodeParams mode l)≤patchStart mode l :=
    endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  have firstSource : (nodeParams mode l).source+max (nodeParams mode l).size mode.wordBytes≤l.start ∨ codeEnd mode l≤(nodeParams mode l).source := by
    have width : mode.wordBytes≤nodeSpan mode := by cases mode <;> decide
    change l.sourceNode+max (nodeSpan mode) mode.wordBytes≤l.start ∨ codeEnd mode l≤l.sourceNode
    rw [max_eq_left width]
    rcases r.nodeOutside with early | late
    · exact Or.inl early
    · exact Or.inr (endInput.trans late)
  have secondSource : (transitionParams mode l).source+max (transitionParams mode l).size mode.wordBytes≤l.start ∨ codeEnd mode l≤(transitionParams mode l).source := by
    have width : mode.wordBytes≤transitionSpan mode := by cases mode <;> decide
    change l.sourceTransition+max (transitionSpan mode) mode.wordBytes≤l.start ∨ codeEnd mode l≤l.sourceTransition
    rw [max_eq_left width]
    rcases r.transitionOutside with early | late
    · exact Or.inl early
    · exact Or.inr (endInput.trans late)
  have first := patch_macro mode l (nodeParams mode l) state firstReady (patches_initial mode l v _ current)
    firstEnd firstSource (le_refl _)
  have seed := StringTemplateStates.at_prefix mode _ _ [] state (by simpa only [List.append_nil] using first)
  rw [StringWrites.run_lift_string,program_run] at seed
  have second := patch_macro mode l (transitionParams mode l) (Listing8CopyTrace.first mode l state) secondReady seed
    (le_refl _) secondSource (by omega)
  simp only [Listing8MainCopies.program,Listing8CopyTrace.program,List.map_append,StringTemplateStates.append,
    StringWrites.run_lift_string,program_run]
  exact ⟨first,second⟩

end SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun
