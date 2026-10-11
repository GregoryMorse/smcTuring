module
public import SmcTuring.Appendix.Listing8JointResetCatalog

public section
namespace SmcTuring.Appendix.Listing8JointResetObserverRun
open Native Listing8CopyImage Listing8SourceGraph Listing8JointDeclarationCatalog Listing8OwnerTemplateCollection
open Listing8ResetLayout Listing8ResetEffects
abbrev Targets:=Listing8PointerCopies.Targets
abbrev region (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (g : Graph):=Listing8LoopHaltImage.region mode origin l g
@[expose] def Placed (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (g : Graph) (address count : Nat) :=
  address+count≤patchStart mode l ∨
  (codeEnd mode l≤address ∧ address+count≤Listing8FullTableImage.start mode origin) ∨
  (Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)≤address ∧
    address+count≤Listing8GraphLayout.input mode origin g.transitions)
@[expose] def Certificate (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) :=
  ∃ packet : StringWrites.Packet,
    (packet.bytes=[] ∨ (packet.address=StringInit.field mode (ownerPC mode (region mode origin l g)) ∨
      packet.address=(region mode origin l g).ttape) ∧ packet.bytes.length=mode.wordBytes) ∧
    ∀ template∈Owners mode origin l v g,Outside mode template packet → Intact mode template memory ∧ Decodes mode template memory
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

theorem empty (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (current : All mode (Owners mode origin l v g) memory) : Certificate mode origin l v g memory :=
  ⟨⟨0,[]⟩,Or.inl rfl,fun template member _ => ⟨current template member,decodes mode template memory (current template member)⟩⟩

theorem from_initializer (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (v : Values mode) (g : Graph) (initial memory : ByteMemory.Memory)
    (current : Listing8JointInitializerCatalog.Certificate mode (ownerPC mode (region mode origin l g))
      (region mode origin l g).ttape (Owners mode origin l v g) initial memory) : Certificate mode origin l v g memory := by
  obtain ⟨packet,allowed,_,headers⟩ := current
  exact ⟨packet,allowed,headers⟩

theorem fields (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode (region mode origin l g) address count)
    (nonTarget : address≠(region mode origin l g).ttape) : Placed mode origin l g address count := by
  have cursors := Listing8JointResetCatalog.cursor_ends mode l ctx.body.state.head.input.fields
  have bounds := (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
  have calls := Listing8GlobalControlLayout.ordered mode origin
  have before := (Listing8GlobalMainBounds.copy mode origin l t g node rule ctx).2
  have order := Listing8JointLocalCatalog.ordering mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have codeBefore := ctx.resources.inputAfter
  have resetEnd : endPC mode (region mode origin l g)=Listing8GraphLayout.input mode origin g.transitions := by
    rw [region,Listing8LoopHaltImage.region,Listing8GraphReset.actual_region mode origin l t _ _ ctx.boot ctx.body,table_length]
    exact Listing8GraphReset.endpoint mode origin g.transitions
  have ownerEnd : StringInit.field mode (ownerPC mode (region mode origin l g))+mode.wordBytes≤endPC mode (region mode origin l g) := by
    cases mode <;> dsimp only [StringInit.field,StringCodec.fieldOffset,Mode.wordBytes,ownerPC,inputCopy,
      transitionCopy,markerPC,endPC,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC,
      ConversionLayout.exchangeSize,ConversionLayout.storeSize,StringCodec.initialSize] <;> omega
  have ownerStart : (region mode origin l g).start≤StringInit.field mode (ownerPC mode (region mode origin l g)) := by
    dsimp only [StringInit.field,ownerPC,inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
  have markerStart : (region mode origin l g).start≤markerPC mode (region mode origin l g)+6 := by
    dsimp only [markerPC,transitionCopy,ownerPC,inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
  have sourceLower : codeEnd mode l≤(region mode origin l g).inputSource := by
    change codeEnd mode l≤(Listing8JointLocalCatalog.failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start+10+StringCodec.fieldOffset mode
    omega
  simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · right;left
    change codeEnd mode l≤Listing8JumpLayout.callPC mode origin+1 ∧ Listing8JumpLayout.callPC mode origin+1+4≤Listing8FullTableImage.start mode origin
    constructor <;> omega
  · right;left
    have inputBound := bounds.inputSourceBeforeCall
    change (region mode origin l g).inputSource+mode.wordBytes≤Listing8JumpLayout.callPC mode origin+1 at inputBound
    exact ⟨sourceLower,by omega⟩
  · exact Or.inl cursors.1
  · right;right
    change (region mode origin l g).start≤StringInit.field mode (ownerPC mode (region mode origin l g)) ∧ _
    exact ⟨ownerStart,ownerEnd.trans (le_of_eq resetEnd)⟩
  · exact False.elim (nonTarget rfl)
  · exact Or.inl cursors.2
  · right;right
    change (region mode origin l g).start≤markerPC mode (region mode origin l g)+6 ∧ _
    refine ⟨markerStart,?_⟩
    rw [←resetEnd]
    change markerPC mode (region mode origin l g)+6+4≤markerPC mode (region mode origin l g)+10
    omega

theorem all_states (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (current : All mode (Owners mode origin l (values mode origin g node rule) g) state.principal.memory)
    (writes : StringStoreRegions.Run mode (Placed mode origin l g) forms state) :
    StringTemplateStates.Run mode (fun reached => All mode (Owners mode origin l (values mode origin g node rule) g) reached.principal.memory) forms state :=
  StringStoreTemplateRuns.preserve mode _ _ forms state current
    (fun memory address bytes kept placed => Listing8JointResetCatalog.observer_store mode origin l t g node rule ctx memory address bytes kept placed) writes


theorem call_not_target (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (_ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    (region mode origin l g).callPC+1≠(region mode origin l g).ttape := by
  have ordered := Listing8GlobalControlLayout.ordered mode origin
  change Listing8JumpLayout.callPC mode origin+1≠Listing8FullTableImage.start mode origin
  omega

theorem input_not_target (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    (region mode origin l g).inputSource≠(region mode origin l g).ttape ∧
    (region mode origin l g).inputCursor≠(region mode origin l g).ttape := by
  have bounds := (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
  have calls := Listing8GlobalControlLayout.ordered mode origin
  have wordPositive : 0<mode.wordBytes := by cases mode <;> decide
  have upper := bounds.inputSourceBeforeCall
  have cursor := Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources
  have codeBefore := Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  constructor
  · change (region mode origin l g).inputSource≠Listing8FullTableImage.start mode origin
    change (region mode origin l g).inputSource+mode.wordBytes≤Listing8JumpLayout.callPC mode origin+1 at upper
    omega
  · change l.input.cursor≠Listing8FullTableImage.start mode origin
    omega

theorem call_states (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (region mode origin l g).start)
    (current : All mode (Owners mode origin l (values mode origin g node rule) g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => All mode (Owners mode origin l (values mode origin g node rule) g) reached.principal.memory)
      (([StringDword.store mode (storeDisp mode (region mode origin l g)) (original (region mode origin l g))]).map (StringStoreWrites.liftDword mode)) state := by
  let r := region mode origin l g
  have bounds := (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
  have fits : r.callPC+1<2^(8*mode.wordBytes) := by have cap := bounds.callFits; change r.callPC+5≤2^(8*mode.wordBytes) at cap; omega
  have write := StringStoreWrites.located mode (r.callPC+1) (r.callPC+5) r.start (r.callPC+1) (original r) state entry
    bounds.storeRange fits ⟨le_refl _,by omega⟩
  have placed := fields mode origin l t g node rule ctx (r.callPC+1) 4
    (by simp [r,Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields]) (call_not_target mode origin l t g node rule ctx)
  have first := BoundedStoreRegions.packet mode (Placed mode origin l g) (r.callPC+1) 4 _ state write
    (StringStoreWrites.length mode _ _ _) placed
  exact all_states mode origin l t g node rule ctx _ state current ⟨first,True.intro⟩

theorem input_states (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (region mode origin l g).start)
    (current : All mode (Owners mode origin l (values mode origin g node rule) g) (afterStore mode (region mode origin l g) state).principal.memory) :
    StringTemplateStates.Run mode (fun reached => All mode (Owners mode origin l (values mode origin g node rule) g) reached.principal.memory)
      ((StringDwordCopy.wordProgram mode (inputCopy mode (region mode origin l g))).map (StringStoreWrites.liftDword mode))
      (afterStore mode (region mode origin l g) state) := by
  let r := region mode origin l g
  have bounds := (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
  have atCopy : (afterStore mode r state).principal.pc=Arithmetic.encodeNat mode (inputCopy mode r).start := by
    rw [store_effect mode r bounds state entry]
  have nonTarget := input_not_target mode origin l t g node rule ctx
  have first := fields mode origin l t g node rule ctx r.inputSource mode.wordBytes
    (by simp [r,Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields]) nonTarget.1
  have second := fields mode origin l t g node rule ctx r.inputCursor mode.wordBytes
    (by simp [r,Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields]) nonTarget.2
  exact all_states mode origin l t g node rule ctx _ _ current
    (WordCopyStoreRegions.regions mode (Placed mode origin l g) (inputCopy mode r) bounds.inputValid _ atCopy first second)

theorem owner_states (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (region mode origin l g).start)
    (image : Listing8ResetPackets.Initial mode (region mode origin l g) state.principal.memory)
    (current : All mode (Owners mode origin l (values mode origin g node rule) g) (afterInput mode (region mode origin l g) state).principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin l (values mode origin g node rule) g reached.principal.memory)
      ((StringInit.forms mode (ownerPC mode (region mode origin l g)) (region mode origin l g).ttape).map (StringWrites.liftString mode))
      (afterInput mode (region mode origin l g) state) := by
  let r := region mode origin l g
  have bounds := (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
  have atOwner : (afterInput mode r state).principal.pc=Arithmetic.encodeNat mode (ownerPC mode r) := by
    rw [input_effect mode r bounds state entry]
  have fits : r.ttape<2^(8*mode.wordBytes) := by have upper := bounds.ttapeFits; change r.ttape+mode.wordBytes<2^(8*mode.wordBytes) at upper; omega
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached active => from_initializer mode origin l _ g (afterInput mode r state).principal.memory reached.principal.memory active)
    (Listing8JointInitializerCatalog.initializer mode (ownerPC mode r) r.ttape _ _ atOwner
      (owner_capacity mode r bounds) fits (owner_current mode r bounds state entry image) current)


/-- The five actual reset phases share one observer certificate. Intermediate
seeds are obtained from executed endpoints, including positive initializer restoration. -/
theorem complete (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (region mode origin l g).start)
    (image : Listing8ResetPackets.Initial mode (region mode origin l g) state.principal.memory)
    (current : All mode (Owners mode origin l (values mode origin g node rule) g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin l (values mode origin g node rule) g reached.principal.memory)
      ((program mode (region mode origin l g)).map (StringStoreWrites.liftDword mode)) state := by
  let r := region mode origin l g
  have bounds := (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
  have coords := positions mode r
  have firstRun : StringWrites.run mode (([StringDword.store mode (storeDisp mode r) (original r)]).map (StringStoreWrites.liftDword mode)) state=
      afterStore mode r state := rfl
  have inputEntry : (afterStore mode r state).principal.pc=Arithmetic.encodeNat mode (inputCopy mode r).start := by
    rw [store_effect mode r bounds state entry]
  have inputPacket : ByteMemory.bytesAt (afterStore mode r state).principal.memory (inputCopy mode r).start
      (WordCopyPacket.bytes mode (inputCopy mode r)).length=WordCopyPacket.bytes mode (inputCopy mode r) := by
    rw [Listing8ResetTrace.store_window mode r bounds state entry _ _ (by dsimp [inputCopy];omega)]
    exact Listing8ResetPackets.input_current mode r _ image
  have secondRun := StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (WordCopyPacket.trace mode (inputCopy mode r) bounds.inputValid (afterStore mode r state) inputEntry inputPacket))
  change StringWrites.run mode ((StringDwordCopy.wordProgram mode (inputCopy mode r)).map (StringStoreWrites.liftDword mode))
    (afterStore mode r state)=afterInput mode r state at secondRun
  have thirdRun : StringWrites.run mode (((StringInit.forms mode (ownerPC mode r) r.ttape).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))
      (afterInput mode r state)=afterOwner mode r state := by
    rw [List.map_map];change StringWrites.run mode ((StringInit.forms mode (ownerPC mode r) r.ttape).map (StringWrites.liftString mode)) _=_
    exact StringWrites.run_lift_string mode _ _
  have transitionEntry : (afterOwner mode r state).principal.pc=Arithmetic.encodeNat mode (transitionCopy mode r).start := by
    rw [owner_effect mode r bounds state entry image]
  have transitionPacket : ByteMemory.bytesAt (afterOwner mode r state).principal.memory (transitionCopy mode r).start
      (WordCopyPacket.bytes mode (transitionCopy mode r)).length=WordCopyPacket.bytes mode (transitionCopy mode r) := by
    rw [owner_effect mode r bounds state entry image,input_window mode r bounds state entry _ _ (by
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega)]
    exact Listing8ResetPackets.transition_current mode r _ image
  have fourthRun := StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (WordCopyPacket.trace mode (transitionCopy mode r) bounds.transitionValid (afterOwner mode r state) transitionEntry transitionPacket))
  change StringWrites.run mode ((StringDwordCopy.wordProgram mode (transitionCopy mode r)).map (StringStoreWrites.liftDword mode))
    (afterOwner mode r state)=afterTransition mode r state at fourthRun
  have first := call_states mode origin l t g node rule ctx state entry current
  have afterFirst := StringTemplateStates.at_prefix mode _ _ [] state (by simpa only [List.append_nil] using first)
  rw [firstRun] at afterFirst
  have second := input_states mode origin l t g node rule ctx state entry afterFirst
  have afterSecond := StringTemplateStates.at_prefix mode _ _ [] (afterStore mode r state)
    (by simpa only [List.append_nil] using second)
  rw [secondRun] at afterSecond
  have third := owner_states mode origin l t g node rule ctx state entry image afterSecond
  have afterThird : All mode (Owners mode origin l (values mode origin g node rule) g) (afterOwner mode r state).principal.memory := by
    rw [owner_effect mode r bounds state entry image]
    exact afterSecond
  have sourcePlaced := fields mode origin l t g node rule ctx (StringInit.field mode (ownerPC mode r)) mode.wordBytes
    (by simp [r,Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields]) (by
      change StringInit.field mode (ownerPC mode r)≠r.ttape
      have positive : 0<mode.wordBytes := by cases mode <;> decide
      have lower : r.start<StringInit.field mode (ownerPC mode r) := by
        dsimp only [StringInit.field,ownerPC,inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
      have cap : r.ttape≤r.start := by
        change Listing8FullTableImage.start mode origin≤Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)
        unfold Listing8TransitionTable.endPC;omega
      omega)
  have targetPlaced := fields mode origin l t g node rule ctx r.transitionCursor mode.wordBytes
    (by simp [r,Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields]) (by
      have early := (Listing8JointResetCatalog.cursor_ends mode l ctx.body.state.head.input.fields).2
      change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤patchStart mode l at early
      have before := Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
      have between := destinations mode l
      have destLower : patchStart mode l+40=(nodeParams mode l).destination := rfl
      change StringCodec.sourceField mode (secondStart mode l)≠Listing8FullTableImage.start mode origin
      have positive : 0<mode.wordBytes := by cases mode <;> decide
      omega)
  have fourth := all_states mode origin l t g node rule ctx _ _ afterThird
    (WordCopyStoreRegions.regions mode (Placed mode origin l g) (transitionCopy mode r) bounds.transitionValid _ transitionEntry sourcePlaced targetPlaced)
  have afterFourth := StringTemplateStates.at_prefix mode _ _ [] (afterOwner mode r state)
    (by simpa only [List.append_nil] using fourth)
  rw [fourthRun] at afterFourth
  have markerEntry : (afterTransition mode r state).principal.pc=Arithmetic.encodeNat mode (markerPC mode r) := by
    rw [transition_effect mode r bounds state entry image]
  have markerFits : markerPC mode r+6<2^(8*mode.wordBytes) := by
    have cap := bounds.capacity
    change endPC mode r<2^(8*mode.wordBytes) at cap
    dsimp only [endPC] at cap;omega
  have lastOwned := StringStoreWrites.located mode (markerPC mode r+6) (markerPC mode r+10) (markerPC mode r) (markerPC mode r+6) 0
    (afterTransition mode r state) markerEntry (fun _ => DwordOwner.reach _) markerFits ⟨le_refl _,by omega⟩
  have markerPlaced := fields mode origin l t g node rule ctx (markerPC mode r+6) 4
    (by simp [r,Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields]) (by
      change markerPC mode r+6≠r.ttape
      have lower : r.start<markerPC mode r+6 := by
        dsimp only [markerPC,transitionCopy,ownerPC,inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
      have positive : 0<mode.wordBytes := by cases mode <;> decide
      have cap : r.ttape≤r.start := by
        change Listing8FullTableImage.start mode origin≤Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)
        unfold Listing8TransitionTable.endPC;omega
      omega)
  have last := all_states mode origin l t g node rule ctx
    ((Listing8OriginalOwners.forms mode (marker mode r)).map (StringStoreWrites.liftDword mode)) _ afterFourth
    ⟨BoundedStoreRegions.packet mode (Placed mode origin l g) (markerPC mode r+6) 4 _ _ lastOwned
      (StringStoreWrites.length mode _ _ _) markerPlaced,trivial⟩
  have liftEmpty := fun forms reached (kept : StringTemplateStates.Run mode
    (fun s => All mode (Owners mode origin l (values mode origin g node rule) g) s.principal.memory) forms reached) =>
      StringTemplateStates.monotone mode _ _ forms reached
        (fun s all => empty mode origin l _ g s.principal.memory all) kept
  change StringTemplateStates.Run mode _ ((program mode r).map (StringStoreWrites.liftDword mode)) state
  rw [program,List.map_append,List.map_append,List.map_append,List.map_append,
    StringTemplateStates.append,StringTemplateStates.append,StringTemplateStates.append,StringTemplateStates.append]
  simp only [StringWrites.run_append,firstRun,secondRun,thirdRun,fourthRun]
  refine ⟨⟨⟨⟨liftEmpty _ _ first,liftEmpty _ _ second⟩,?_⟩,liftEmpty _ _ fourth⟩,liftEmpty _ _ last⟩
  have lifting : (fun form : StringForm.Form mode => StringStoreWrites.liftDword mode (StringDword.Form.string form))=StringWrites.liftString mode := by funext form;rfl
  simpa only [List.map_map,Function.comp_def,lifting] using third


/-- At the actual terminal reset prefixes, the complete inactive executable
catalog and executing reset/global decoders share the same precise owner packet. -/
theorem maintained (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached =>
      Inactive mode origin l g reached.principal.memory ∧
      Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory ∧
      (∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),DwordTemplateCollection.Decodes mode template reached.principal.memory) ∧
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory ∧
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8ResetExecutableTemplates.Decodes mode (region mode origin l g) reached.principal.memory ∧
      Certificate mode origin l (values mode origin g node rule) g reached.principal.memory)
      ((program mode (region mode origin l g)).map (StringStoreWrites.liftDword mode))
      (Listing8LoopTable.finish mode origin l t g node rule state) := by
  have seed : All mode (Owners mode origin l (values mode origin g node rule) g)
      (Listing8LoopTable.finish mode origin l t g node rule state).principal.memory := by
    rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1]
    exact (Listing8JointDeclarationCatalog.endpoint_seed mode origin l t g node rule ctx old state image.control).2
  have owners := complete mode origin l t g node rule ctx _
    (Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted)
    (Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted) seed
  have catalogs := Listing8JointResetCatalog.maintained mode origin l t g node rule ctx old state image halted
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached pair =>
    ⟨pair.1.1,pair.1.2.1,pair.1.2.2.1,pair.1.2.2.2.1,pair.1.2.2.2.2.1,
      pair.1.2.2.2.2.2.1,pair.1.2.2.2.2.2.2,pair.2⟩)
    (JointTemplateStates.join mode _ _ _ _ catalogs owners)

end SmcTuring.Appendix.Listing8JointResetObserverRun
