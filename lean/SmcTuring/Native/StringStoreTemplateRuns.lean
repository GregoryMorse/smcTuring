module
public import SmcTuring.Native.StringStoreRegions
public import SmcTuring.Native.StringInitTemplates
public import SmcTuring.Native.ControlPacketWrites

public section
namespace SmcTuring.Native.StringStoreTemplateRuns

theorem native (mode : Mode) (allowed : Nat → Nat → Prop) (forms : List (Native.Form mode))
    (state : StringExecution.State mode)
    (owned : Writes.OwnedRun mode (fun address => allowed address.toNat mode.wordBytes) forms state.principal) :
    StringStoreRegions.Run mode allowed (forms.map (StringWrites.liftNative mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    constructor
    · change allowed (Writes.address mode form state.principal).toNat
        (LittleEndian.wordEncode mode.wordBytes (Writes.value mode form state.principal)).length
      simpa only [LittleEndian.word_encode_length] using owned.1
    · exact ih (StringStack.execute mode (StringWrites.liftNative mode form) state) owned.2

theorem initializer (mode : Mode) (allowed : Nat → Nat → Prop) (start value : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (valueFits : value+mode.wordBytes<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start value)
    (labelOwned : allowed (StringInit.field mode start) mode.wordBytes) (targetOwned : allowed value mode.wordBytes) :
    StringStoreRegions.Run mode allowed ((StringInit.forms mode start value).map (StringWrites.liftString mode)) state := by
  have fieldFits : StringInit.field mode start<2^(8*mode.wordBytes) := by
    cases mode <;> simp [StringInit.field,StringCodec.fieldOffset,StringCodec.initialSize,Mode.wordBytes] at fits ⊢ <;> omega
  have pointer := StringInit.initialized_pointer mode start value state.principal.memory fits current
  cases mode with
  | x86 =>
    constructor
    · change allowed (Arithmetic.encodeNat .x86 (StringInit.field .x86 start)).toNat
        (LittleEndian.wordEncode 4 (BitVec.ofNat 32 value)).length
      rw [Arithmetic.encode_nat_toNat .x86 _ fieldFits,LittleEndian.word_encode_length]
      exact labelOwned
    · trivial
  | x64 =>
    have readerPointer : Execution.load .x64 state.principal.memory (ReaderImage.label .x64 start)=Arithmetic.encodeNat .x64 value := pointer
    have fields := Reader.four_writes_owned .x64 state.principal (ReaderImage.label .x64 start)
      (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64)
      (ReaderImage.first_hits .x64 start state.principal entry) (ReaderImage.second_hits .x64 start state.principal entry)
      (fun address => allowed address.toNat Mode.x64.wordBytes)
      (by change allowed (Arithmetic.encodeNat .x64 (StringInit.field .x64 start)).toNat 8
          rw [Arithmetic.encode_nat_toNat .x64 _ fieldFits];exact labelOwned)
      (by rw [readerPointer,Arithmetic.encode_nat_toNat .x64 value (by change value<2^64;change value+8<2^64 at valueFits;omega)];exact targetOwned)
    have actual : Writes.OwnedRun .x64 (fun address => allowed address.toNat Mode.x64.wordBytes)
        [.memory .exchangeAcc (ReaderImage.firstDisp .x64 start),Reader.storeForm .x64 (ReaderImage.label .x64 start) (ReaderImage.secondDisp .x64),
          .exchangeIndirect,.moffs (Arithmetic.encodeNat .x64 value)] state.principal := by
      rw [←readerPointer]
      simpa only [Writes.OwnedRun,and_true,Reader.swapped,Reader.restored,Reader.dereferenced] using fields
    have lifted := native .x64 allowed _ state actual
    simpa only [StringInit.forms,StringInit.first_displacement,StringInit.second_displacement,
      ReaderImage.firstDisp,ReaderImage.secondDisp,Reader.storeForm,List.map_cons,List.map_nil,StringWrites.liftNative] using lifted

theorem control (mode : Mode) (allowed : Nat → Nat → Prop) (sites : List ControlPackets.Site) (start : Nat)
    (chain : ControlPackets.Contiguous mode start sites) (valid : ∀ site∈sites,ControlPackets.Valid mode site)
    (fields : ∀ site∈sites,allowed site.target (ControlPackets.width mode site))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringStoreRegions.Run mode allowed ((ControlPackets.program mode sites).map StringStack.Form.previous) state := by
  induction sites generalizing start state with
  | nil => trivial
  | cons site rest ih =>
    have v := valid site (List.Mem.head _)
    have here : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    constructor
    · change allowed (StringWrites.packet mode (.previous (ControlPackets.form mode site)) state).address
        (StringWrites.packet mode (.previous (ControlPackets.form mode site)) state).bytes.length
      rw [ControlPacketWrites.address mode site v state here,ControlPacketWrites.length]
      exact fields site (List.Mem.head _)
    · change StringStoreRegions.Run mode allowed _ (StringControl.execute mode (ControlPackets.form mode site) state)
      rw [ControlPackets.execute_effect mode site v state here]
      exact ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
        (fun later member => fields later (List.Mem.tail _ member)) (ControlPackets.effect mode site state) rfl

theorem preserve (mode : Mode) (allowed : Nat → Nat → Prop) (property : ByteMemory.Memory → Prop)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode) (initial : property state.principal.memory)
    (stable : ∀ memory address packet,property memory → allowed address packet.length → property (ByteMemory.putBytes memory address packet))
    (regions : StringStoreRegions.Run mode allowed forms state) :
    StringTemplateStates.Run mode (fun reached => property reached.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact initial
  | cons form rest ih =>
    have kept : property (StringStack.execute mode form state).principal.memory := by
      rw [StringWrites.execute_memory]
      exact stable _ _ _ initial regions.1
    exact ⟨initial,ih _ kept regions.2⟩

end SmcTuring.Native.StringStoreTemplateRuns
