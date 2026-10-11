module
public import SmcTuring.Appendix.Listing8JointOriginalGraphState

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphSentinel
open Native Listing8SourceGraph Listing8Prototypes Listing8OwnerTemplateCollection
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Certificate (mode : Mode) (origin : Nat) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,
    (packet.bytes=[] ∨ packet.address=nodePC mode origin g g.halt ∧ packet.bytes.length=mode.wordBytes) ∧
    ∀ template∈Listing8OriginalGraphCatalog.catalog mode origin g,Outside mode template packet →
      Intact mode template memory ∧ Decodes mode template memory

theorem empty (mode : Mode) (origin : Nat) (g : Graph) (memory : ByteMemory.Memory)
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory) : Certificate mode origin g memory :=
  ⟨⟨0,[]⟩,Or.inl rfl,fun template member _ => ⟨current template member,Listing8OwnerTemplateCollection.decodes mode template memory (current template member)⟩⟩

theorem x64_forms (start target : Nat) :
    StringInit.forms .x64 start target=Listing8CopiedPointer.forms .x64 start start (Arithmetic.encodeNat .x64 target) := by
  simp only [StringInit.forms,StringInit.first_displacement,StringInit.second_displacement,
    Listing8CopiedPointer.forms,Listing8CopiedPointer.first,Listing8CopiedPointer.second,
    ReaderImage.firstDisp,ReaderImage.secondDisp]
  rfl

theorem x64_bytes (start target : Nat) :
    StringInit.bytes .x64 start target=pointerBytes .x64 start (Arithmetic.encodeNat .x64 target) := by
  rw [←StringInit.forms_encoding,x64_forms]
  exact Listing8CopiedPointer.encoding .x64 start start _

theorem from_reader (origin start : Nat) (g : Graph) (initial memory : ByteMemory.Memory)
    (early : start+StringCodec.initialSize .x64≤Listing8FullTableImage.start .x64 origin)
    (fits : nodePC .x64 origin g g.halt<2^(8*Mode.x64.wordBytes))
    (current : Listing8CopiedPointerActiveRegions.Certificate .x64 start start
      (Arithmetic.encodeNat .x64 (nodePC .x64 origin g g.halt))
      (Listing8OriginalGraphCatalog.catalog .x64 origin g) initial memory) : Certificate .x64 origin g memory := by
  obtain ⟨packet,allowed,_,headers⟩:=current
  rcases allowed with restored | ⟨addresses,size⟩
  · exact ⟨packet,Or.inl restored,headers⟩
  · rcases addresses with self | target
    · apply empty .x64 origin g memory
      intro template member
      have late:=Listing8OriginalGraphInputFields.lower .x64 origin g template member
      have outside : Outside .x64 template packet := by
        left
        rw [self,size]
        change start+19+8≤Listing8OwnerTemplateCollection.start .x64 template
        change start+27≤Listing8FullTableImage.start .x64 origin at early
        omega
      exact (headers template member outside).1
    · rw [Arithmetic.encode_nat_toNat .x64 _ fits] at target
      exact ⟨packet,Or.inr ⟨target,size⟩,headers⟩

theorem initializer (mode : Mode) (origin start : Nat) (g : Graph) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (early : start+StringCodec.initialSize mode≤Listing8FullTableImage.start mode origin)
    (sentinelFits : nodePC mode origin g g.halt<2^(8*mode.wordBytes))
    (packet : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=
      StringInit.bytes mode start (nodePC mode origin g g.halt))
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin g reached.principal.memory)
      ((StringInit.forms mode start (nodePC mode origin g g.halt)).map (StringWrites.liftString mode)) state := by
  cases mode with
  | x86 =>
    have ending : (StringWrites.run .x86
        ((StringInit.forms .x86 start (nodePC .x86 origin g g.halt)).map (StringWrites.liftString .x86)) state).principal.memory=state.principal.memory := by
      rw [StringWrites.run_lift_string,StringInit.effect .x86 start _ state entry fits packet]
    simp only [StringInit.forms,List.map_cons,List.map_nil,StringTemplateStates.Run]
    change Certificate .x86 origin g state.principal.memory ∧
      Certificate .x86 origin g (StringWrites.run .x86
        ((StringInit.forms .x86 start (nodePC .x86 origin g g.halt)).map (StringWrites.liftString .x86)) state).principal.memory
    rw [ending]
    exact ⟨empty .x86 origin g _ current,empty .x86 origin g _ current⟩
  | x64 =>
    have image : ByteMemory.bytesAt state.principal.memory start
        (pointerBytes .x64 start (Arithmetic.encodeNat .x64 (nodePC .x64 origin g g.halt))).length=
          pointerBytes .x64 start (Arithmetic.encodeNat .x64 (nodePC .x64 origin g g.halt)) := by
      rw [pointer_length]
      rw [x64_bytes] at packet
      exact packet
    rw [x64_forms]
    exact StringTemplateStates.monotone .x64 _ _ _ state
      (fun reached exactRegion => from_reader origin start g state.principal.memory reached.principal.memory early sentinelFits exactRegion)
      (Listing8CopiedPointerActiveRegions.run .x64 start start _ _ state current entry fits fits image image)

theorem restored (mode : Mode) (origin start : Nat) (g : Graph) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (packet : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=
      StringInit.bytes mode start (nodePC mode origin g g.halt))
    (current : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    (StringExecution.run mode (StringInit.forms mode start (nodePC mode origin g g.halt)) state).principal.memory=state.principal.memory ∧
      Certificate mode origin g (StringExecution.run mode (StringInit.forms mode start (nodePC mode origin g g.halt)) state).principal.memory := by
  rw [StringInit.effect mode start _ state entry fits packet]
  exact ⟨rfl,empty mode origin g _ current⟩

end SmcTuring.Appendix.Listing8OriginalGraphSentinel
