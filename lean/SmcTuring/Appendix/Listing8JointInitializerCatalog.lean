module
public import SmcTuring.Appendix.Listing8JointDeclarationCatalog

public section
namespace SmcTuring.Appendix.Listing8JointInitializerCatalog
open Native Listing8OwnerTemplateCollection
attribute [local irreducible] StringTemplateStates.Run

/-- The sole modification is exactly the initializer's self operand or its
original referent word. Empty certifies actual whole-memory restoration. -/
@[expose] def Certificate (mode : Mode) (start target : Nat) (templates : List (Template mode))
    (initial memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,
    (packet.bytes=[] ∨ (packet.address=StringInit.field mode start ∨ packet.address=target) ∧ packet.bytes.length=mode.wordBytes) ∧
    memory=ByteMemory.putBytes initial packet.address packet.bytes ∧
    ∀ template∈templates,Outside mode template packet → Intact mode template memory ∧ Decodes mode template memory

theorem empty (mode : Mode) (start target : Nat) (templates : List (Template mode)) (memory : ByteMemory.Memory)
    (current : All mode templates memory) : Certificate mode start target templates memory memory := by
  have same : ByteMemory.putBytes memory 0 []=memory := by
    funext position;simp [ByteMemory.putBytes,ByteMemory.Inside]
  exact ⟨⟨0,[]⟩,Or.inl rfl,same.symm,fun template member _ =>
    ⟨current template member,decodes mode template memory (current template member)⟩⟩

theorem from_reader (start target : Nat) (templates : List (Template .x64)) (initial memory : ByteMemory.Memory)
    (fits : target<2^(8*Mode.x64.wordBytes))
    (current : Listing8CopiedPointerActiveRegions.Certificate .x64 start start (Arithmetic.encodeNat .x64 target)
      templates initial memory) : Certificate .x64 start target templates initial memory := by
  obtain ⟨packet,allowed,snapshot,headers⟩ := current
  refine ⟨packet,?_,snapshot,headers⟩
  rcases allowed with restored | ⟨address,size⟩
  · exact Or.inl restored
  · right
    constructor
    · rcases address with self | referent
      · exact Or.inl self
      · rw [Arithmetic.encode_nat_toNat .x64 _ fits] at referent
        exact Or.inr referent
    · exact size

/-- All observed catalogs share the SAME actual initializer prefix and its
one exact temporary word; no later image or full-run premise is supplied. -/
theorem initializer (mode : Mode) (start target : Nat) (templates : List (Template mode))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (targetFits : target<2^(8*mode.wordBytes))
    (packet : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start target)
    (current : All mode templates state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode start target templates state.principal.memory reached.principal.memory)
      ((StringInit.forms mode start target).map (StringWrites.liftString mode)) state := by
  cases mode with
  | x86 =>
    have ending : (StringWrites.run .x86 ((StringInit.forms .x86 start target).map (StringWrites.liftString .x86)) state).principal.memory=state.principal.memory := by
      rw [StringWrites.run_lift_string,StringInit.effect .x86 start target state entry fits packet]
    simp only [StringInit.forms,List.map_cons,List.map_nil,StringTemplateStates.Run]
    change Certificate .x86 start target templates state.principal.memory state.principal.memory ∧
      Certificate .x86 start target templates state.principal.memory
        (StringWrites.run .x86 ((StringInit.forms .x86 start target).map (StringWrites.liftString .x86)) state).principal.memory
    rw [ending]
    exact ⟨empty .x86 start target templates _ current,empty .x86 start target templates _ current⟩
  | x64 =>
    have image : ByteMemory.bytesAt state.principal.memory start
        (Listing8Prototypes.pointerBytes .x64 start (Arithmetic.encodeNat .x64 target)).length=
        Listing8Prototypes.pointerBytes .x64 start (Arithmetic.encodeNat .x64 target) := by
      rw [Listing8Prototypes.pointer_length]
      rw [Listing8OriginalGraphSentinel.x64_bytes] at packet
      exact packet
    rw [Listing8OriginalGraphSentinel.x64_forms]
    exact StringTemplateStates.monotone .x64 _ _ _ state
      (fun reached active => from_reader start target templates state.principal.memory reached.principal.memory targetFits active)
      (Listing8CopiedPointerActiveRegions.run .x64 start start _ templates state current entry fits fits image image)

theorem restored (mode : Mode) (start target : Nat) (templates : List (Template mode))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (packet : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start target)
    (current : All mode templates state.principal.memory) :
    (StringExecution.run mode (StringInit.forms mode start target) state).principal.memory=state.principal.memory ∧
    Certificate mode start target templates state.principal.memory
      (StringExecution.run mode (StringInit.forms mode start target) state).principal.memory := by
  rw [StringInit.effect mode start target state entry fits packet]
  exact ⟨rfl,empty mode start target templates _ current⟩

end SmcTuring.Appendix.Listing8JointInitializerCatalog
