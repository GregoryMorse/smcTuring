module
public import SmcTuring.Native.MixedFixedTemplates
public import SmcTuring.Native.MixedFieldOwnership
public import SmcTuring.Native.DwordPacketWrites

public section
namespace SmcTuring.Native.DwordPacketTemplateRuns
open DwordPackets

@[expose] def template (site : Site) : DwordTemplateCollection.Template :=
  match site.operation with
  | .store => .binary .store site.pc
  | .bitXor => .binary .bitXor site.pc
  | .bitAnd => .binary .bitAnd site.pc
  | .bitOr => .binary .bitOr site.pc
  | .complement => .unary .complement site.pc

theorem initial (mode : Mode) (sites : List Site) (memory : ByteMemory.Memory)
    (headers : DwordPackets.Intact mode sites memory) :
    DwordTemplateCollection.All (sites.map template) memory := by
  intro descriptor member
  rcases List.mem_map.mp member with ⟨site,inside,rfl⟩
  have packet := DwordPackets.current mode site memory (headers site inside)
  cases site with
  | mk pc operation target =>
    cases operation
    all_goals simp only [template,DwordTemplateCollection.Intact]
    all_goals simp only [live,form,raw,DwordArithmetic.located,DwordArithmetic.relocate] at packet
    · exact DwordOperandTemplates.initial .store pc _ _ memory packet
    · exact DwordOperandTemplates.initial .bitXor pc _ _ memory packet
    · exact DwordOperandTemplates.initial .bitAnd pc _ _ memory packet
    · exact DwordOperandTemplates.initial .bitOr pc _ _ memory packet
    · exact DwordUnaryTemplates.initial .complement pc _ memory packet

theorem located (mode : Mode) (site : Site) (valid : Valid mode site)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode site.pc)
    (owns : Nat → Nat → Prop) (field : owns site.target 4) :
    owns (MixedDword.address mode (.arithmetic (live mode site state.memory)) state).toNat
      (MixedDword.width mode (.arithmetic (live mode site state.memory))) := by
  apply MixedFieldOwnership.located mode site.pc site.target (raw site.operation (DwordCode.get state.memory (site.pc+6)))
    state (by cases site with | mk pc op target => cases op <;> rfl) entry
  · have length : DwordArithmetic.length (raw site.operation (DwordCode.get state.memory (site.pc+6)))=size site := by
      cases site with | mk pc op target => cases op <;> rfl
    simpa only [length] using valid.2.2
  · exact valid.2.1
  · exact field

/-- Only original descriptor bytes and static complete target windows are
inputs. Every later PC and live instruction value is derived by execution. -/
theorem all_states (mode : Mode) (templates : List DwordTemplateCollection.Template)
    (sites : List Site) (start : Nat) (chain : Contiguous start sites)
    (valid : ∀ site∈sites,Valid mode site)
    (fields : ∀ site∈sites,DwordTemplateCollection.CompatibleAll templates site.target 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (intact : DwordTemplateCollection.All templates state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => DwordTemplateCollection.All templates reached.principal.memory)
      ((DwordPackets.program mode sites state.principal).map (StringStoreWrites.liftDword mode)) state := by
  induction sites generalizing start state with
  | nil => exact intact
  | cons site rest ih =>
    have v := valid site (List.Mem.head _)
    have here : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have target := located mode site v state.principal here _ (fields site (List.Mem.head _))
    have kept := DwordTemplateCollection.execute mode templates (.arithmetic (live mode site state.principal.memory)) state intact target
    have next : (DwordPackets.execute mode site state.principal).pc=Arithmetic.encodeNat mode (site.pc+size site) := by
      rw [DwordPackets.effect mode site v state.principal here]
    constructor
    · exact intact
    · change StringTemplateStates.Run mode _ _ (StringDword.execute mode (StringDwordArithmetic.canonical mode (live mode site state.principal.memory)) state)
      change DwordTemplateCollection.All templates
        (StringDword.execute mode (StringDwordArithmetic.canonical mode (live mode site state.principal.memory)) state).principal.memory at kept
      rw [StringDwordArithmetic.execute] at kept ⊢
      exact ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
        (fun later member => fields later (List.Mem.tail _ member)) _ next kept

theorem fixed_states (mode : Mode) (templates : List (MixedFixedTemplates.Entry mode))
    (sites : List Site) (start : Nat) (chain : Contiguous start sites)
    (valid : ∀ site∈sites,Valid mode site)
    (fields : ∀ site∈sites,MixedFixedTemplates.OutsideAll mode templates site.target 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (intact : MixedFixedTemplates.All mode templates state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => MixedFixedTemplates.All mode templates reached.principal.memory)
      ((DwordPackets.program mode sites state.principal).map (StringStoreWrites.liftDword mode)) state := by
  induction sites generalizing start state with
  | nil => exact intact
  | cons site rest ih =>
    have v := valid site (List.Mem.head _)
    have here : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have target := located mode site v state.principal here _ (fields site (List.Mem.head _))
    have kept := MixedFixedTemplates.execute mode templates (.arithmetic (live mode site state.principal.memory)) state intact target
    have next : (DwordPackets.execute mode site state.principal).pc=Arithmetic.encodeNat mode (site.pc+size site) := by
      rw [DwordPackets.effect mode site v state.principal here]
    constructor
    · exact intact
    · change StringTemplateStates.Run mode _ _ (StringDword.execute mode (StringDwordArithmetic.canonical mode (live mode site state.principal.memory)) state)
      change MixedFixedTemplates.All mode templates
        (StringDword.execute mode (StringDwordArithmetic.canonical mode (live mode site state.principal.memory)) state).principal.memory at kept
      rw [StringDwordArithmetic.execute] at kept ⊢
      exact ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
        (fun later member => fields later (List.Mem.tail _ member)) _ next kept

end SmcTuring.Native.DwordPacketTemplateRuns
