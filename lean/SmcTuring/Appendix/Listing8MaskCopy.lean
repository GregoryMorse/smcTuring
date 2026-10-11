module
public import SmcTuring.Appendix.InputUpdate
public import SmcTuring.Native.DwordImage
public import SmcTuring.X64.HalfWords

public section
namespace SmcTuring.Appendix.Listing8MaskCopy
open Native
abbrev Dword := BitVec 32

/-- The printed AND instruction's start holds opcode/address bytes, not its
zero/all-ones immediate. This closed kernel counterexample uses zero displacement. -/
theorem printed_source_counterexample :
    DwordCode.get
      (ByteMemory.putBytes (fun _ => 0) 0 (DwordArithmetic.encode (.bitAnd 0 0))) 0 =
      (0x2581#32) := by decide

theorem printed_source_is_not_zero_mask : (0x2581#32) ≠ InputUpdate.mask false := by decide
theorem printed_source_is_not_true_mask : (0x2581#32) ≠ InputUpdate.mask true := by decide

/-- For every displacement and comparison result, the instruction-start
DWORD cannot be the intended mask: its leading opcode bytes are 81 25. -/
theorem instruction_start_not_mask (memory : ByteMemory.Memory) (pc : Nat)
    (displacement : Dword) (condition : Bool)
    (current : ByteMemory.bytesAt memory pc
      (DwordArithmetic.encode (.bitAnd displacement (InputUpdate.mask condition))).length =
      DwordArithmetic.encode (.bitAnd displacement (InputUpdate.mask condition))) :
    DwordCode.get memory pc ≠ InputUpdate.mask condition := by
  intro same
  have header := ByteWindow.packet memory pc [] [0x81,0x25]
    (LittleEndian.wordEncode 4 displacement ++ LittleEndian.wordEncode 4 (InputUpdate.mask condition))
    (by simpa only [DwordArithmetic.encode,List.nil_append,List.append_assoc] using current)
  have encoded := LittleEndian.word_encode_decode 4 _ _ (DwordCode.read_total memory pc)
  change LittleEndian.wordEncode 4 (DwordCode.get memory pc) = ByteMemory.bytesAt memory pc 4 at encoded
  rw [same] at encoded
  have firstBytes := congrArg (List.take 2) encoded
  rw [Fetch.bytes_at_take memory pc 4 2 (by decide)] at firstBytes
  simp only [List.nil_append,Nat.add_zero,List.length_cons,List.length_nil] at header
  rw [header] at firstBytes
  cases condition <;> simp [InputUpdate.mask,LittleEndian.wordEncode,LittleEndian.encode] at firstBytes

/-- The exact immediate field to pass as the source is pc+IMMOFFS, six bytes
after the instruction start in both bare DWORD forms. -/
theorem mask_operand (memory : ByteMemory.Memory) (pc : Nat) (displacement : Dword)
    (condition : Bool)
    (current : ByteMemory.bytesAt memory pc
      (DwordArithmetic.encode (.bitAnd displacement (InputUpdate.mask condition))).length =
      DwordArithmetic.encode (.bitAnd displacement (InputUpdate.mask condition))) :
    DwordCode.get memory (pc+6) = InputUpdate.mask condition := by
  have packet := ByteWindow.packet memory pc
    ([0x81,0x25] ++ LittleEndian.wordEncode 4 displacement)
    (LittleEndian.wordEncode 4 (InputUpdate.mask condition)) []
    (by simpa only [DwordArithmetic.encode,List.append_nil] using current)
  have operand : ByteMemory.bytesAt memory (pc+6) 4 =
      LittleEndian.wordEncode 4 (InputUpdate.mask condition) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,
      LittleEndian.word_encode_length] using packet
  have decoded : ByteMemory.readWord .x86 memory (pc+6) = some (InputUpdate.mask condition) := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt memory (pc+6) 4) = _
    rw [operand,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem repeated_mask (condition : Bool) :
    X64.HalfWords.pack (InputUpdate.mask condition) (InputUpdate.mask condition) =
      if condition then BitVec.allOnes 64 else 0 := by
  cases condition <;> rfl

/-- The corrected low-half call works in both modes: its source argument is
the complete AND immediate, and the three actual packets restore that source. -/
theorem copy_mask_correct (mode : Mode) (layout : DwordLayout.Layout)
    (valid : DwordLayout.Admissible mode layout) (condition : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (image : DwordImage.Intact mode layout state.memory)
    (mask : DwordCode.get state.memory layout.source = InputUpdate.mask condition) :
    DwordCode.Trace mode state (DwordLayout.program mode layout)
      (DwordEffects.finish mode layout state) ∧
    DwordCode.get (DwordEffects.finish mode layout state).memory layout.destination =
      InputUpdate.mask condition ∧
    DwordCode.get (DwordEffects.finish mode layout state).memory layout.source =
      InputUpdate.mask condition := by
  exact ⟨DwordImage.trace mode layout valid state entry image,
    (DwordEffects.destination_value mode layout valid state entry).trans mask,
    (DwordEffects.source_value mode layout valid state entry).trans mask⟩

structure Layout where
  start : Nat
  source : Nat
  low : Nat
  high : Nat

@[expose] def first (layout : Layout) : DwordLayout.Layout :=
  { start := layout.start, source := layout.source, destination := layout.low }
@[expose] def second (layout : Layout) : DwordLayout.Layout :=
  { start := DwordLayout.endPC .x64 (first layout), source := layout.source, destination := layout.high }
@[expose] def finish (layout : Layout) (state : Execution.State .x64) : Execution.State .x64 :=
  DwordEffects.finish .x64 (second layout) (DwordEffects.finish .x64 (first layout) state)
@[expose] def program (layout : Layout) : List (DwordCode.Form .x64) :=
  DwordLayout.program .x64 (first layout) ++ DwordLayout.program .x64 (second layout)

/-- Static separation/range conditions for the two literal DWORD copy helpers.
The high half reads the same mask word: the corrected source stride is zero. -/
structure Valid (layout : Layout) : Prop where
  firstValid : DwordLayout.Admissible .x64 (first layout)
  secondValid : DwordLayout.Admissible .x64 (second layout)
  lowOutsideSecond : layout.low+4 ≤ (second layout).start ∨
    DwordLayout.endPC .x64 (second layout) ≤ layout.low
  halves : layout.low+4 ≤ layout.high ∨ layout.high+4 ≤ layout.low

theorem trace_append {state middle final : Execution.State .x64}
    {first second : List (DwordCode.Form .x64)}
    (before : DwordCode.Trace .x64 state first middle)
    (after : DwordCode.Trace .x64 middle second final) :
    DwordCode.Trace .x64 state (first++second) final := by
  induction before with
  | nil => exact after
  | step current rest ih => exact .step current (ih after)

theorem second_entry (layout : Layout) (valid : Valid layout)
    (state : Execution.State .x64) (entry : state.pc = Arithmetic.encodeNat .x64 layout.start) :
    (DwordEffects.finish .x64 (first layout) state).pc =
      Arithmetic.encodeNat .x64 (second layout).start := by
  rw [DwordEffects.effect .x64 (first layout) valid.firstValid state entry]
  rfl

theorem second_intact (layout : Layout) (valid : Valid layout)
    (state : Execution.State .x64) (entry : state.pc = Arithmetic.encodeNat .x64 layout.start)
    (initial : DwordImage.Intact .x64 (second layout) state.memory) :
    DwordImage.Intact .x64 (second layout)
      (DwordEffects.finish .x64 (first layout) state).memory := by
  rw [DwordEffects.effect .x64 (first layout) valid.firstValid state entry]
  exact DwordImage.intact_put .x64 (second layout) state.memory initial layout.low _
    valid.lowOutsideSecond

theorem effect (layout : Layout) (valid : Valid layout)
    (state : Execution.State .x64) (entry : state.pc = Arithmetic.encodeNat .x64 layout.start) :
    finish layout state =
      { state with
        pc := Arithmetic.encodeNat .x64 (DwordLayout.endPC .x64 (second layout))
        accumulator := DwordCode.lift .x64 (DwordCode.low .x64 state.accumulator)
        memory := DwordCode.put
          (DwordCode.put state.memory layout.low (DwordCode.get state.memory layout.source))
          layout.high (DwordCode.get state.memory layout.source) } := by
  rw [finish,DwordEffects.effect .x64 (second layout) valid.secondValid _
    (second_entry layout valid state entry)]
  have restored := DwordEffects.source_value .x64 (first layout) valid.firstValid state entry
  change DwordCode.get (DwordEffects.finish .x64 (first layout) state).memory layout.source =
    DwordCode.get state.memory layout.source at restored
  simp only [second]
  rw [restored,DwordEffects.effect .x64 (first layout) valid.firstValid state entry,
    DwordCode.low_lift]
  rfl

theorem trace (layout : Layout) (valid : Valid layout)
    (state : Execution.State .x64) (entry : state.pc = Arithmetic.encodeNat .x64 layout.start)
    (firstImage : DwordImage.Intact .x64 (first layout) state.memory)
    (secondImage : DwordImage.Intact .x64 (second layout) state.memory) :
    DwordCode.Trace .x64 state (program layout) (finish layout state) :=
  trace_append (DwordImage.trace .x64 (first layout) valid.firstValid state entry firstImage)
    (DwordImage.trace .x64 (second layout) valid.secondValid _ (second_entry layout valid state entry)
      (second_intact layout valid state entry secondImage))

/-- Both destination halves receive the actual comparison mask. Source bytes
are restored by each helper and every future helper fetch follows from the
two initial packet images and static separation. -/
theorem broadcast_correct (layout : Layout) (valid : Valid layout) (condition : Bool)
    (state : Execution.State .x64) (entry : state.pc = Arithmetic.encodeNat .x64 layout.start)
    (firstImage : DwordImage.Intact .x64 (first layout) state.memory)
    (secondImage : DwordImage.Intact .x64 (second layout) state.memory)
    (mask : DwordCode.get state.memory layout.source = InputUpdate.mask condition) :
    DwordCode.Trace .x64 state (program layout) (finish layout state) ∧
    X64.HalfWords.pack
      (DwordCode.get (finish layout state).memory layout.low)
      (DwordCode.get (finish layout state).memory layout.high) =
      if condition then BitVec.allOnes 64 else 0 := by
  refine ⟨trace layout valid state entry firstImage secondImage,?_⟩
  rw [effect layout valid state entry]
  have lowFrame : ∀ index : Fin 4, ¬ByteMemory.Inside layout.high 4 (layout.low+index.val) := by
    intro index
    have bound := index.isLt
    simp only [ByteMemory.Inside]
    rcases valid.halves with before | after <;> omega
  rw [DwordCode.get_frame _ _ _ _ lowFrame,DwordCode.get_put,DwordCode.get_put,mask]
  exact repeated_mask condition

/-- The two printed mask-copy calls emit one helper each in x86 mode and
two helpers each in x64 mode. Their source is the later AND immediate. -/
@[expose] def distributionLayouts (mode : Mode) (start source transition direction : Nat) :
    List DwordLayout.Layout :=
  match mode with
  | .x86 =>
    [{ start := start, source := source, destination := transition },
     { start := start+17, source := source, destination := direction }]
  | .x64 =>
    [{ start := start, source := source, destination := transition },
     { start := start+18, source := source, destination := transition+10 },
     { start := start+36, source := source, destination := direction },
     { start := start+54, source := source, destination := direction+10 }]

@[expose] def copyBytes (mode : Mode) (layout : DwordLayout.Layout) : List LittleEndian.Byte :=
  DwordCode.encode mode (DwordLayout.first mode layout) ++
    DwordCode.encode mode (DwordLayout.second mode layout) ++
    DwordCode.encode mode (DwordLayout.third mode layout)
@[expose] def distributionBytes (mode : Mode) (start source transition direction : Nat) :
    List LittleEndian.Byte :=
  (distributionLayouts mode start source transition direction).flatMap (copyBytes mode)

theorem copy_length (mode : Mode) (layout : DwordLayout.Layout) :
    (copyBytes mode layout).length = DwordLayout.span mode := by
  simp only [copyBytes,List.length_append,DwordCode.encode_length,
    (DwordLayout.lengths mode layout).1,(DwordLayout.lengths mode layout).2.1,
    (DwordLayout.lengths mode layout).2.2]
  cases mode <;> rfl

theorem distribution_length (mode : Mode) (start source transition direction : Nat) :
    (distributionBytes mode start source transition direction).length =
      if mode = .x86 then 34 else 72 := by
  cases mode <;> simp [distributionBytes,distributionLayouts,copy_length,
    DwordLayout.span,DwordLayout.storeSize]

theorem literal_input_offsets (mode : Mode) (start source transition direction : Nat) :
    (if mode = .x86 then 66 else 67) +
      (distributionBytes mode start source transition direction).length =
      (if mode = .x86 then 100 else 139) ∧
    (if mode = .x86 then 66 else 67) +
      (distributionBytes mode start source transition direction).length + InputUpdate.span mode =
      (if mode = .x86 then 139 else 180) := by
  rw [distribution_length]
  cases mode <;> decide

end SmcTuring.Appendix.Listing8MaskCopy
