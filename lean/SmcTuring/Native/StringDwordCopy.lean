module
public import SmcTuring.Native.StringDword
public import SmcTuring.Native.ConversionImage
public import SmcTuring.Native.DwordMixedImage

public section
namespace SmcTuring.Native.StringDwordCopy

@[expose] def native (mode : Mode) (form : Native.Form mode) : StringDword.Form mode := .string (.native form)
@[expose] def copy (mode : Mode) (form : DwordCode.Form mode) : StringDword.Form mode :=
  match mode,form with
  | .x86,.exchange d => native .x86 (.memory .exchangeAcc d)
  | .x86,.store d => native .x86 (.memory .storeAcc d)
  | .x86,.moffs address => native .x86 (.moffs address)
  | .x64,form => .mixed (.copy form)

theorem native_encoding (mode : Mode) (form : Native.Form mode) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (Native.encode mode form).length = Native.encode mode form) :
    StringDword.fetch mode memory pc = some (native mode form) :=
  StringDword.string_fetch mode memory pc (.native form) (StringForm.fetch_current_encoding mode memory pc (.native form) (by trivial) current)

theorem native_execute (mode : Mode) (form : Native.Form mode) (state : StringExecution.State mode) :
    StringDword.execute mode (native mode form) state = { state with principal := Execution.execute mode form state.principal } := rfl

theorem low_x86 (value : Word .x86) : DwordCode.low .x86 value = value := by
  change BitVec.ofNat 32 value.toNat = value
  exact BitVec.ofNat_toNat 32 value

theorem lift_x86 (value : BitVec 32) : DwordCode.lift .x86 value = value := by
  change BitVec.ofNat 32 value.toNat = value
  exact BitVec.ofNat_toNat 32 value

theorem copy_encoding (mode : Mode) (form : DwordCode.Form mode) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (DwordCode.encode mode form).length = DwordCode.encode mode form) :
    StringDword.fetch mode memory pc = some (copy mode form) := by
  cases mode with
  | x86 =>
    cases form with
    | exchange d => exact native_encoding .x86 (.memory .exchangeAcc d) memory pc current
    | store d => exact native_encoding .x86 (.memory .storeAcc d) memory pc current
    | moffs address => exact native_encoding .x86 (.moffs address) memory pc current
  | x64 =>
    have bound : 3 ≤ (DwordCode.encode .x64 form).length := by
      rw [DwordCode.encode_length];cases form <;> simp [DwordCode.length,Mode.wordBytes]
    have noLength : StringForm.lengthOfBytes .x64 (ByteMemory.bytesAt memory pc 3) = none := by
      rw [←Fetch.bytes_at_take memory pc _ 3 bound,current]
      cases form <;> rfl
    have noString : StringForm.fetch .x64 memory pc = none := by rw [StringForm.fetch,noLength];rfl
    rw [StringDword.fetch,noString,MixedDword.copy_encoding .x64 memory pc form current]
    rfl

theorem copy_execute (mode : Mode) (form : DwordCode.Form mode) (state : StringExecution.State mode) :
    StringDword.execute mode (copy mode form) state = { state with principal := DwordCode.execute mode form state.principal } := by
  cases mode with
  | x86 =>
    cases form <;> simp [copy,native,StringDword.execute,StringExecution.execute,DwordCode.execute,
      Execution.execute,Execution.executeMemory,Execution.storeState,Execution.load,Execution.nextPC,
      DwordCode.address,DwordCode.next,DwordCode.length,Native.instructionLength,wordPrefix,MemoryOp.prefix,
      MemoryOp.trailer,Mode.wordBytes,DwordCode.get,DwordCode.put,ByteMemory.putWord,low_x86,lift_x86]
  | x64 => rfl

@[expose] def wordProgram (mode : Mode) (layout : ConversionLayout.Layout) := (ConversionLayout.program mode layout).map (native mode)
@[expose] def wordFinish (mode : Mode) (layout : ConversionLayout.Layout) (state : StringExecution.State mode) :=
  { state with principal := ConversionEffects.finish mode layout state.principal }
@[expose] def dwordProgram (mode : Mode) (layout : DwordLayout.Layout) := (DwordLayout.program mode layout).map (copy mode)
@[expose] def dwordFinish (mode : Mode) (layout : DwordLayout.Layout) (state : StringExecution.State mode) :=
  { state with principal := DwordEffects.finish mode layout state.principal }

theorem word_trace (mode : Mode) (layout : ConversionLayout.Layout) (valid : ConversionLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode layout.start)
    (current : ControlImage.Intact mode (ConversionLayout.entries mode layout) state.principal.memory) :
    StringDword.Trace mode state (wordProgram mode layout) (wordFinish mode layout state) := by
  have fetched (pc : Nat) (form : Native.Form mode) (st : StringExecution.State mode)
      (member : (⟨pc,.fixed form⟩ : ControlImage.Entry mode) ∈ ConversionLayout.entries mode layout)
      (current : ControlImage.Intact mode (ConversionLayout.entries mode layout) st.principal.memory)
      (location : st.principal.pc = Arithmetic.encodeNat mode pc) (below : pc ≤ ConversionLayout.endPC mode layout) :
      StringDword.fetch mode st.principal.memory st.principal.pc.toNat = some (native mode form) := by
    have fits : pc < 2^(8*mode.wordBytes) := by have cap := valid.codeFits;omega
    rw [location,Arithmetic.encode_nat_toNat mode pc fits]
    exact native_encoding mode form _ pc (current ⟨pc,.fixed form⟩ member)
  let first := {state with principal := ConversionEffects.swapped mode layout state.principal}
  let second := {state with principal := ConversionEffects.stored mode layout state.principal}
  have a := fetched layout.start (ConversionLayout.first mode layout) state (List.Mem.head _) current entry (by unfold ConversionLayout.endPC ConversionLayout.thirdPC ConversionLayout.secondPC;omega)
  have b := fetched (ConversionLayout.secondPC mode layout) (ConversionLayout.second mode layout) first (List.Mem.tail _ (List.Mem.head _))
    (ConversionImage.swapped_intact mode layout valid state.principal current entry) (ConversionEffects.swapped_pc mode layout valid state.principal entry)
    (by unfold ConversionLayout.endPC ConversionLayout.thirdPC;omega)
  have c := fetched (ConversionLayout.thirdPC mode layout) (ConversionLayout.third mode layout) second (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    (ConversionImage.stored_intact mode layout valid state.principal current entry) (ConversionEffects.stored_pc mode layout valid state.principal entry)
    (by unfold ConversionLayout.endPC;omega)
  change StringDword.Trace mode state [native mode (ConversionLayout.first mode layout),native mode (ConversionLayout.second mode layout),native mode (ConversionLayout.third mode layout)] _
  refine .step a ?_
  rw [native_execute]
  change StringDword.Trace mode first [native mode (ConversionLayout.second mode layout),native mode (ConversionLayout.third mode layout)] _
  refine .step b ?_
  rw [native_execute]
  change StringDword.Trace mode second [native mode (ConversionLayout.third mode layout)] _
  refine .step c ?_
  rw [native_execute]
  exact .nil _

theorem dword_trace (mode : Mode) (layout : DwordLayout.Layout) (valid : DwordLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode layout.start)
    (current : DwordImage.Intact mode layout state.principal.memory) :
    StringDword.Trace mode state (dwordProgram mode layout) (dwordFinish mode layout state) := by
  have fetched (pc : Nat) (form : DwordCode.Form mode) (st : StringExecution.State mode)
      (location : st.principal.pc = Arithmetic.encodeNat mode pc) (fits : pc < 2^(8*mode.wordBytes))
      (packet : ByteMemory.bytesAt st.principal.memory pc (DwordCode.encode mode form).length = DwordCode.encode mode form) :
      StringDword.fetch mode st.principal.memory st.principal.pc.toNat = some (copy mode form) := by
    rw [location,Arithmetic.encode_nat_toNat mode pc fits]
    exact copy_encoding mode form _ pc packet
  have firstPacket := current ⟨layout.start,.fixed (DwordImage.firstCode mode layout)⟩ (List.Mem.head _)
  change ByteMemory.bytesAt state.principal.memory layout.start (Native.encode .x86 (DwordImage.firstCode mode layout)).length = Native.encode .x86 (DwordImage.firstCode mode layout) at firstPacket
  rw [←(DwordImage.byte_bindings mode layout).1] at firstPacket
  have startFits : layout.start < 2^(8*mode.wordBytes) := by have cap := valid.codeFits;unfold DwordLayout.endPC DwordLayout.thirdPC DwordLayout.secondPC at cap;omega
  have a := fetched layout.start (DwordLayout.first mode layout) state entry startFits firstPacket
  let first := {state with principal := DwordEffects.swapped mode layout state.principal}
  let second := {state with principal := DwordEffects.stored mode layout state.principal}
  have firstImage := DwordImage.swapped_intact mode layout valid state.principal entry current
  have secondPacket := firstImage ⟨DwordLayout.secondPC mode layout,.fixed (DwordImage.secondCode mode layout)⟩ (List.Mem.tail _ (List.Mem.head _))
  change ByteMemory.bytesAt first.principal.memory (DwordLayout.secondPC mode layout) (Native.encode .x86 (DwordImage.secondCode mode layout)).length = Native.encode .x86 (DwordImage.secondCode mode layout) at secondPacket
  rw [←(DwordImage.byte_bindings mode layout).2.1] at secondPacket
  have secondFits : DwordLayout.secondPC mode layout < 2^(8*mode.wordBytes) := by have cap := valid.codeFits;unfold DwordLayout.endPC DwordLayout.thirdPC at cap;omega
  have b := fetched (DwordLayout.secondPC mode layout) (DwordLayout.second mode layout) first (DwordEffects.swapped_pc mode layout valid state.principal entry) secondFits secondPacket
  have secondImage := DwordImage.stored_intact mode layout valid state.principal entry current
  have thirdPacket := secondImage ⟨DwordLayout.thirdPC mode layout,.fixed (DwordImage.thirdCode mode layout)⟩ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  change ByteMemory.bytesAt second.principal.memory (DwordLayout.thirdPC mode layout) (Native.encode .x86 (DwordImage.thirdCode mode layout)).length = Native.encode .x86 (DwordImage.thirdCode mode layout) at thirdPacket
  rw [←(DwordImage.byte_bindings mode layout).2.2] at thirdPacket
  have thirdFits : DwordLayout.thirdPC mode layout < 2^(8*mode.wordBytes) := by have cap := valid.codeFits;unfold DwordLayout.endPC at cap;omega
  have c := fetched (DwordLayout.thirdPC mode layout) (DwordLayout.third mode layout) second (DwordEffects.stored_pc mode layout valid state.principal entry) thirdFits thirdPacket
  change StringDword.Trace mode state [copy mode (DwordLayout.first mode layout),copy mode (DwordLayout.second mode layout),copy mode (DwordLayout.third mode layout)] _
  refine .step a ?_
  rw [copy_execute]
  change StringDword.Trace mode first [copy mode (DwordLayout.second mode layout),copy mode (DwordLayout.third mode layout)] _
  refine .step b ?_
  rw [copy_execute]
  change StringDword.Trace mode second [copy mode (DwordLayout.third mode layout)] _
  refine .step c ?_
  rw [copy_execute]
  exact .nil _

end SmcTuring.Native.StringDwordCopy
