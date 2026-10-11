module
public import SmcTuring.Native.DwordUnaryTemplates
public import SmcTuring.Native.StringTemplateStates
public import SmcTuring.Native.MixedWriteRuns

public section
namespace SmcTuring.Native.DwordTemplateCollection

inductive Template where
  | binary (kind : DwordOperandTemplates.Kind) (pc : Nat)
  | unary (kind : DwordUnaryTemplates.Kind) (pc : Nat)
  deriving DecidableEq, Repr
@[expose] def start : Template → Nat
  | .binary _ pc | .unary _ pc => pc
@[expose] def span : Template → Nat
  | .binary _ _ => 10
  | .unary kind _ => DwordUnaryTemplates.span kind
@[expose] def field : Template → Nat
  | .binary _ pc => pc+2
  | .unary kind pc => DwordUnaryTemplates.field kind pc
@[expose] def width : Template → Nat
  | .binary _ _ => 8
  | .unary _ _ => 4
@[expose] def Intact (template : Template) (memory : ByteMemory.Memory) : Prop :=
  match template with
  | .binary kind pc => DwordOperandTemplates.Intact kind pc memory
  | .unary kind pc => DwordUnaryTemplates.Intact kind pc memory
@[expose] def currentForm (mode : Mode) (template : Template) (memory : ByteMemory.Memory) : StringStack.Form mode :=
  StringStoreWrites.liftDword mode (StringMixed.canonical mode (.arithmetic (match template with
  | .binary kind pc => DwordOperandTemplates.form kind (DwordCode.get memory (pc+2)) (DwordCode.get memory (pc+6))
  | .unary kind pc => DwordUnaryTemplates.form kind (DwordCode.get memory (DwordUnaryTemplates.field kind pc)))))
@[expose] def Decodes (mode : Mode) (template : Template) (memory : ByteMemory.Memory) : Prop :=
  StringStack.fetch mode memory (start template)=some (currentForm mode template memory)
@[expose] def All (templates : List Template) (memory : ByteMemory.Memory) : Prop :=
  ∀ template∈templates,Intact template memory
@[expose] def Compatible (template : Template) (address count : Nat) : Prop :=
  (field template≤address ∧ address+count≤field template+width template) ∨
    (address+count≤start template ∨ start template+span template≤address)
@[expose] def CompatibleAll (templates : List Template) (address count : Nat) : Prop :=
  ∀ template∈templates,Compatible template address count

theorem field_bounds (template : Template) :
    start template≤field template ∧ field template+width template≤start template+span template := by
  cases template with
  | binary kind pc => simp only [start,field,width,span];omega
  | unary kind pc => simp only [start,field,width,span,DwordUnaryTemplates.field,DwordUnaryTemplates.span];omega

theorem decodes (mode : Mode) (template : Template) (memory : ByteMemory.Memory)
    (intact : Intact template memory) : Decodes mode template memory := by
  cases template with
  | binary kind pc => exact DwordOperandTemplates.decodes mode kind pc memory intact
  | unary kind pc => exact DwordUnaryTemplates.decodes mode kind pc memory intact

theorem store (template : Template) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Intact template memory) (compatible : Compatible template address packet.length) :
    Intact template (ByteMemory.putBytes memory address packet) := by
  cases template with
  | binary kind pc =>
    rcases compatible with within | outside
    · exact (DwordOperandTemplates.mutable_store kind pc memory address packet intact within.1 (by
        have upper := within.2
        change address+packet.length≤pc+2+8 at upper
        omega)).1
    · exact DwordOperandTemplates.frame kind pc memory address packet intact outside
  | unary kind pc =>
    rcases compatible with within | outside
    · exact DwordUnaryTemplates.mutable_store kind pc memory address packet intact within.1 within.2
    · exact DwordUnaryTemplates.frame kind pc memory address packet intact outside

theorem store_all (templates : List Template) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : All templates memory) (compatible : CompatibleAll templates address packet.length) :
    All templates (ByteMemory.putBytes memory address packet) :=
  fun template member => store template memory address packet (intact template member) (compatible template member)

theorem execute (mode : Mode) (templates : List Template) (form : MixedDword.Form mode) (state : StringExecution.State mode)
    (intact : All templates state.principal.memory)
    (compatible : CompatibleAll templates (MixedDword.address mode form state.principal).toNat (MixedDword.width mode form)) :
    All templates (StringStack.execute mode (StringStoreWrites.liftDword mode (StringMixed.canonical mode form)) state).principal.memory := by
  rw [StringWrites.execute_memory]
  apply store_all templates state.principal.memory _ _ intact
  simpa only [StringMixedWrites.address,StringMixedWrites.length] using compatible

/-- A proved complete store certificate preserves every original descriptor
at every actual reached state, including stores inside native helper macros. -/
theorem all_states (mode : Mode) (templates : List Template) (forms : List (MixedDword.Form mode))
    (state : StringExecution.State mode) (intact : All templates state.principal.memory)
    (owned : MixedDword.OwnedRun mode (CompatibleAll templates) forms state.principal) :
    StringTemplateStates.Run mode (fun current => All templates current.principal.memory)
      ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    have kept := execute mode templates form state intact owned.1
    constructor
    · exact intact
    · change StringTemplateStates.Run mode _ _ (StringDword.execute mode (StringMixed.canonical mode form) state)
      change All templates (StringDword.execute mode (StringMixed.canonical mode form) state).principal.memory at kept
      rw [StringMixed.execute] at kept ⊢
      exact ih _ kept owned.2

theorem all_decodes (mode : Mode) (templates : List Template) (forms : List (MixedDword.Form mode))
    (state : StringExecution.State mode) (intact : All templates state.principal.memory)
    (owned : MixedDword.OwnedRun mode (CompatibleAll templates) forms state.principal) :
    StringTemplateStates.Run mode (fun current => ∀ template∈templates,Decodes mode template current.principal.memory)
      ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun current all template member => decodes mode template current.principal.memory (all template member))
    (all_states mode templates forms state intact owned)

end SmcTuring.Native.DwordTemplateCollection
