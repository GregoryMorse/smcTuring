module
public import SmcTuring.Appendix.Listing4StackLayout
public import SmcTuring.Native.FixedStackTemplates

public section
namespace SmcTuring.Appendix.Listing4StackTemplates
open Native Listing4StackLayout

@[expose] def front (origin : Nat) := Native.encode .x64 (first origin)++Native.encode .x64 (second origin)++[0x48,0xa3]
@[expose] def middle : List LittleEndian.Byte := [0x48,0xa3]
@[expose] def Intact (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) : Prop :=
  match mode with
  | .x86 => DwordOperandTemplates.Intact .store origin memory
  | .x64 => PairedPayloadTemplate.Intact .x64 memory origin (front origin) middle []
@[expose] def Slots (mode : Mode) (origin address count : Nat) : Prop :=
  (stptr mode origin≤address ∧ address+count≤stptr mode origin+mode.wordBytes) ∨
    (returnField mode origin≤address ∧ address+count≤returnField mode origin+mode.wordBytes)
@[expose] def Allowed (mode : Mode) (origin address count : Nat) : Prop :=
  Slots mode origin address count ∨ (address+count≤origin ∨ origin+size mode≤address)

theorem front_length (origin : Nat) : (front origin).length=16 := by
  simp [front,Native.instruction_length,first,second,StackMemory.form,Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix]

theorem fields (origin : Nat) :
    PairedPayloadTemplate.firstField origin (front origin)=stptr .x64 origin ∧
      PairedPayloadTemplate.secondField .x64 origin (front origin) middle=returnField .x64 origin := by
  simp [PairedPayloadTemplate.firstField,PairedPayloadTemplate.secondField,front_length,middle,stptr,returnField,Mode.wordBytes,Nat.add_assoc]

theorem initial (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory origin (size mode)=Listing4StackLayout.bytes mode origin) : Intact mode origin memory := by
  cases mode with
  | x86 =>
    exact DwordOperandTemplates.initial .store origin (Arithmetic.encodeNat .x86 (stptr .x86 origin))
      (Arithmetic.encodeNat .x86 (stptr .x86 origin)) memory current
  | x64 =>
    apply PairedPayloadTemplate.initial .x64 memory origin (front origin) middle []
      (Arithmetic.encodeNat .x64 (stptr .x64 origin)) (Arithmetic.encodeNat .x64 (stptr .x64 origin))
    have shape : Listing4StackLayout.bytes .x64 origin=front origin++
        LittleEndian.wordEncode Mode.x64.wordBytes (Arithmetic.encodeNat .x64 (stptr .x64 origin))++middle++
        LittleEndian.wordEncode Mode.x64.wordBytes (Arithmetic.encodeNat .x64 (stptr .x64 origin))++[] := by
      simp [front,middle,Listing4StackLayout.bytes,third,fourth,Native.encode,wordPrefix,List.append_assoc]
    rw [←shape,Listing4StackLayout.bytes_length]
    exact current

@[expose] def live (origin : Nat) (memory : ByteMemory.Memory) : List (FixedStackTemplates.Instruction .x64) :=
  [FixedStackTemplates.native .x64 (first origin),FixedStackTemplates.native .x64 (second origin),
    FixedStackTemplates.native .x64 (.moffs (Protected.wordAt .x64 memory (stptr .x64 origin))),
    FixedStackTemplates.native .x64 (.moffs (Protected.wordAt .x64 memory (returnField .x64 origin)))]

theorem current (origin : Nat) (memory : ByteMemory.Memory) (intact : Intact .x64 origin memory) :
    ByteMemory.bytesAt memory origin (FixedStackTemplates.bytes .x64 (live origin memory)).length=
      FixedStackTemplates.bytes .x64 (live origin memory) := by
  have image:=PairedPayloadTemplate.current .x64 memory origin (front origin) middle [] intact
  rw [(fields origin).1,(fields origin).2] at image
  have span : PairedPayloadTemplate.span .x64 (front origin) middle []=34 := by
    simp [PairedPayloadTemplate.span,front_length,middle,Mode.wordBytes]
  rw [span] at image
  have shape : FixedStackTemplates.bytes .x64 (live origin memory)=front origin++
      LittleEndian.wordEncode Mode.x64.wordBytes (Protected.wordAt .x64 memory (stptr .x64 origin))++middle++
      LittleEndian.wordEncode Mode.x64.wordBytes (Protected.wordAt .x64 memory (returnField .x64 origin))++[] := by
    simp [FixedStackTemplates.bytes,live,FixedStackTemplates.encode,FixedStackTemplates.native,StringForm.encode,
      front,middle,Native.encode,wordPrefix,Mode.wordBytes,List.append_assoc]
  rw [shape]
  have length : (front origin++LittleEndian.wordEncode Mode.x64.wordBytes (Protected.wordAt .x64 memory (stptr .x64 origin))++middle++
      LittleEndian.wordEncode Mode.x64.wordBytes (Protected.wordAt .x64 memory (returnField .x64 origin))++[]).length=34 := by
    have a:=LittleEndian.word_encode_length Mode.x64.wordBytes (Protected.wordAt .x64 memory (stptr .x64 origin))
    have b:=LittleEndian.word_encode_length Mode.x64.wordBytes (Protected.wordAt .x64 memory (returnField .x64 origin))
    simp only [List.length_append,front_length,a,b,middle,List.length_cons,List.length_nil]
    rfl
  rw [length]
  exact image

@[expose] def Decodes (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) : Prop :=
  match mode with
  | .x86 => DwordTemplateCollection.Decodes .x86 (.binary .store origin) memory
  | .x64 => ∀ entry∈FixedStackTemplates.place .x64 origin (live origin memory),FixedStackTemplates.Decodes .x64 entry memory

theorem decodes (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (intact : Intact mode origin memory) :
    Decodes mode origin memory := by
  cases mode with
  | x86 => exact DwordTemplateCollection.decodes .x86 (.binary .store origin) memory intact
  | x64 =>
    have all:=FixedStackTemplates.placed_initial .x64 origin (live origin memory) memory (current origin memory intact)
    intro entry member
    apply FixedStackTemplates.decodes .x64 entry memory _ (all entry member)
    exact FixedStackTemplates.placed_legal .x64 origin _ (by simp [live,FixedStackTemplates.Legal,FixedStackTemplates.native,StringForm.Legal]) entry member

/-- Both complete stack operands may contain arbitrary temporary native
values. Their stores preserve every opcode of the original declaration. -/
theorem store (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Intact mode origin memory) (allowed : Allowed mode origin address packet.length) :
    Intact mode origin (ByteMemory.putBytes memory address packet) := by
  rcases allowed with slots | outside
  · cases mode with
    | x86 =>
      apply (DwordOperandTemplates.mutable_store .store origin memory address packet intact ?_ ?_).1
      all_goals simp only [Slots,stptr,returnField,Mode.wordBytes] at slots
      all_goals rcases slots with a | b <;> omega
    | x64 =>
      apply PairedPayloadTemplate.operand_store .x64 memory origin (front origin) middle [] address packet intact
      simpa only [Slots,(fields origin).1,(fields origin).2] using slots
  · cases mode with
    | x86 => exact DwordOperandTemplates.frame .store origin memory address packet intact outside
    | x64 =>
      apply PairedPayloadTemplate.frame .x64 memory origin (front origin) middle [] address packet intact
      simpa [PairedPayloadTemplate.span,front_length,middle,Mode.wordBytes,size] using outside

theorem all_states (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (initial : Intact mode origin state.principal.memory) (regions : StringStoreRegions.Run mode (Allowed mode origin) forms state) :
    StringTemplateStates.Run mode (fun reached => Decodes mode origin reached.principal.memory) forms state :=
  StringTemplateStates.monotone mode _ _ _ state (fun reached intact => decodes mode origin reached.principal.memory intact)
    (StringStoreTemplateRuns.preserve mode (Allowed mode origin) (Intact mode origin) forms state initial (store mode origin) regions)

end SmcTuring.Appendix.Listing4StackTemplates
