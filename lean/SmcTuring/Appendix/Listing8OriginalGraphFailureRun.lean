module
public import SmcTuring.Appendix.Listing8OriginalGraphSentinel

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphFailureRun
open Native Listing8FailureLayout Listing8FailureImage Listing8SourceGraph Listing8OwnerTemplateCollection
attribute [local irreducible] StringTemplateStates.Run
@[expose] def safeFields (mode : Mode) (r : Layout) : List (Nat × Nat) :=
  [(r.cursor,mode.wordBytes),(source mode r,mode.wordBytes),(mask mode r,4),(andPC mode r+6,4),(callPC mode r+1,4)]

theorem before_field (mode : Mode) (origin : Nat) (r : Layout) (bounds : Listing8FailureBounds.Bounds mode r)
    (early : callPC mode r+5≤Listing8FullTableImage.start mode origin)
    (address count : Nat) (member : (address,count)∈safeFields mode r) : address+count≤Listing8FullTableImage.start mode origin := by
  have cursor:=bounds.cursorBefore
  simp only [safeFields,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h <;> cases h
  all_goals cases mode <;> simp only [source,StringInit.field,StringCodec.fieldOffset,mask,callPC,endPC,
    xorPC,andPC,storePC,notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,
    wordPrefix,stackSpan,Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at cursor early ⊢ <;> omega

theorem store (mode : Mode) (origin : Nat) (g : Graph) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte)
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory)
    (early : address+packet.length≤Listing8FullTableImage.start mode origin) :
    All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (ByteMemory.putBytes memory address packet) := by
  intro template member
  exact Listing8OwnerTemplateCollection.frame mode template memory (current template member) ⟨address,packet⟩
    (Or.inl (early.trans (Listing8OriginalGraphInputFields.lower mode origin g template member)))

theorem reset_all (mode : Mode) (origin : Nat) (g : Graph) (r : Layout) (bounds : Listing8FailureBounds.Bounds mode r)
    (early : callPC mode r+5≤Listing8FullTableImage.start mode origin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode r.start)
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (resetState mode r state).principal.memory := by
  change All mode _ (DwordArithmetic.execute mode (reset mode r) state.principal).memory
  rw [Listing8FailureBounds.reset_effect mode r bounds state.principal entry]
  exact store mode origin g _ _ (LittleEndian.wordEncode 4 0) current (by
    rw [LittleEndian.word_encode_length]
    exact before_field mode origin r bounds early _ _ (by simp [safeFields]))

theorem comparison_states (mode : Mode) (origin : Nat) (g : Graph) (r : Layout) (bounds : Listing8FailureBounds.Bounds mode r)
    (early : callPC mode r+5≤Listing8FullTableImage.start mode origin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (comparison mode r).start)
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => All mode (Listing8OriginalGraphCatalog.catalog mode origin g) reached.principal.memory)
      ((Listing8FailComparison.program mode (comparison mode r)).map StringStack.Form.previous) state := by
  have fields : ∀ site∈Listing8FailComparison.sites mode (comparison mode r),
      site.target+ControlPackets.width mode site≤Listing8FullTableImage.start mode origin := by
    intro site member
    apply before_field mode origin r bounds early
    simp only [Listing8FailComparison.sites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [safeFields,Listing8FailComparison.site,Listing8FailComparison.target,Listing8FailComparison.operation,comparison,ControlPackets.width]
  exact StringStoreTemplateRuns.preserve mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
    (All mode (Listing8OriginalGraphCatalog.catalog mode origin g)) _ _ current (store mode origin g)
    (StringStoreTemplateRuns.control mode _ _ _ (Listing8FailComparison.chain mode (comparison mode r))
      (Listing8FailComparison.valid mode (comparison mode r) (Listing8FailureBounds.comparison_bounds mode r bounds)) fields state entry)

theorem post_states (mode : Mode) (origin : Nat) (g : Graph) (r : Layout) (bounds : Listing8FailureBounds.Bounds mode r)
    (early : callPC mode r+5≤Listing8FullTableImage.start mode origin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (notPC mode r))
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => All mode (Listing8OriginalGraphCatalog.catalog mode origin g) reached.principal.memory)
      ((DwordPackets.program mode (post mode r) state.principal).map (StringStoreWrites.liftDword mode)) state := by
  have fields : ∀ site∈post mode r,site.target+4≤Listing8FullTableImage.start mode origin := by
    intro site member
    apply before_field mode origin r bounds early
    simp only [post,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp [safeFields]
  exact StringStoreTemplateRuns.preserve mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
    (All mode (Listing8OriginalGraphCatalog.catalog mode origin g)) _ _ current (store mode origin g)
    (DwordXorRegionRuns.packets mode _ _ _ (post_chain mode r) (Listing8FailureBounds.post_valid mode r bounds) fields state entry)

theorem whole (mode : Mode) (origin : Nat) (g : Graph) (r : Layout) (bounds : Listing8FailureBounds.Bounds mode r)
    (early : callPC mode r+5≤Listing8FullTableImage.start mode origin) (sentinel : r.sentinel=nodePC mode origin g g.halt)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode r.start)
    (image : Listing8FailureReuseImage.Current mode r state.principal.memory)
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8OriginalGraphSentinel.Certificate mode origin g reached.principal.memory)
      ((Listing8FailureTrace.program mode r state).map StringStack.Form.previous) state := by
  have resetAll:=reset_all mode origin g r bounds early state entry current
  have first : StringTemplateStates.Run mode (fun reached => Listing8OriginalGraphSentinel.Certificate mode origin g reached.principal.memory)
      [.previous (.previous (StringDwordArithmetic.canonical mode (reset mode r)))] state := by
    simp only [StringTemplateStates.Run]
    rw [show StringStack.execute mode (.previous (.previous (StringDwordArithmetic.canonical mode (reset mode r)))) state=resetState mode r state from by
      change StringDword.execute mode (StringDwordArithmetic.canonical mode (reset mode r)) state=_
      rw [StringDwordArithmetic.execute];rfl]
    exact ⟨Listing8OriginalGraphSentinel.empty mode origin g _ current,Listing8OriginalGraphSentinel.empty mode origin g _ resetAll⟩
  have ownerEarly : ownerPC r+StringCodec.initialSize mode≤Listing8FullTableImage.start mode origin := by
    cases mode <;> simp only [callPC,endPC,xorPC,andPC,storePC,notPC,comparisonPC,ownerPC,StringCodec.initialSize,
      WordMemoryArithmetic.size,wordPrefix,stackSpan,reduceCtorEq,ite_true,ite_false] at early ⊢ <;> omega
  have sentinelFits : nodePC mode origin g g.halt<2^(8*mode.wordBytes) := by
    have cap:=bounds.sentinelFits;rw [sentinel] at cap;omega
  have ownerImage:=Listing8FailureReuseImage.reset_owner mode r bounds state entry image
  rw [sentinel] at ownerImage
  have second:=Listing8OriginalGraphSentinel.initializer mode origin (ownerPC r) g (resetState mode r state)
    (Listing8FailureImage.reset_pc mode r bounds state entry) (Listing8FailureBounds.owner_fits mode r bounds)
    ownerEarly sentinelFits ownerImage resetAll
  have ownerAll : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (ownerFinish mode r state).principal.memory := by
    rw [Listing8FailureReuseImage.owner_effect mode r bounds state entry image]
    exact resetAll
  have third:=comparison_states mode origin g r bounds early (ownerFinish mode r state)
    (Listing8FailureReuseImage.comparison_entry mode r bounds state entry image) ownerAll
  have thirdRun : StringWrites.run mode ((Listing8FailComparison.program mode (comparison mode r)).map StringStack.Form.previous)
      (ownerFinish mode r state)=comparisonFinish mode r state :=
    ControlPacketWrites.run mode _ _ (Listing8FailComparison.chain mode (comparison mode r))
      (Listing8FailComparison.valid mode (comparison mode r) (Listing8FailureBounds.comparison_bounds mode r bounds)) _
      (Listing8FailureReuseImage.comparison_entry mode r bounds state entry image)
  have comparisonAll:=StringTemplateStates.at_prefix mode _ _ [] (ownerFinish mode r state)
    (by simpa only [List.append_nil] using third)
  rw [thirdRun] at comparisonAll
  have last:=post_states mode origin g r bounds early (comparisonFinish mode r state)
    (Listing8FailureReuseEffects.comparison_endpoint mode r bounds state entry image) comparisonAll
  have firstRun : StringWrites.run mode [.previous (.previous (StringDwordArithmetic.canonical mode (reset mode r)))] state=resetState mode r state := by
    change StringDword.execute mode (StringDwordArithmetic.canonical mode (reset mode r)) state=_
    rw [StringDwordArithmetic.execute];rfl
  have lifting : (fun form : StringForm.Form mode => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))=
      StringWrites.liftString mode := by funext form;rfl
  have secondRun : StringWrites.run mode ((Listing8FailureTrace.ownerProgram mode r).map StringStack.Form.previous)
      (resetState mode r state)=ownerFinish mode r state := by
    rw [Listing8FailureTrace.ownerProgram,List.map_map]
    change StringWrites.run mode ((StringInit.forms mode (ownerPC r) r.sentinel).map (StringWrites.liftString mode)) _=_
    exact StringWrites.run_lift_string mode _ _
  rw [Listing8FailureTrace.program,List.map_append,List.map_append,List.map_append,
    StringTemplateStates.append,StringTemplateStates.append,StringTemplateStates.append]
  simp only [StringWrites.run_append,List.map_cons,List.map_nil,firstRun,secondRun,thirdRun]
  refine ⟨⟨⟨first,?_⟩,StringTemplateStates.monotone mode _ _ _ _
    (fun reached headers => Listing8OriginalGraphSentinel.empty mode origin g reached.principal.memory headers) third⟩,
    StringTemplateStates.monotone mode _ _ _ _
      (fun reached headers => Listing8OriginalGraphSentinel.empty mode origin g reached.principal.memory headers) last⟩
  simpa only [Listing8FailureTrace.ownerProgram,List.map_map,Function.comp_def,lifting,sentinel] using second

theorem endpoint (mode : Mode) (origin : Nat) (g : Graph) (r : Layout) (bounds : Listing8FailureBounds.Bounds mode r)
    (early : callPC mode r+5≤Listing8FullTableImage.start mode origin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode r.start)
    (image : Listing8FailureReuseImage.Current mode r state.principal.memory)
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (finish mode r state).principal.memory := by
  rw [Listing8FailureReuseEffects.memory mode r bounds state entry image]
  have keep (memory : ByteMemory.Memory) (address : Nat) (value : BitVec 32)
      (headers : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory)
      (member : (address,4)∈safeFields mode r) :
      All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (DwordCode.put memory address value) :=
    store mode origin g memory address (LittleEndian.wordEncode 4 value) headers (by
      rw [LittleEndian.word_encode_length];exact before_field mode origin r bounds early address 4 member)
  exact keep _ _ _ (keep _ _ _ (keep _ _ _ current (by simp [safeFields])) (by simp [safeFields])) (by simp [safeFields])

end SmcTuring.Appendix.Listing8OriginalGraphFailureRun
