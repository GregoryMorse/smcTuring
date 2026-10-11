module
public import SmcTuring.Appendix.DwordComparison
public import SmcTuring.Native.MixedDword
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Appendix.DwordComparisonTail
open Native
abbrev Dword := BitVec 32
abbrev Layout := DwordComparison.Layout

/-- `layout.start` is the preceding M14 owner entry. The actual comparison
tail starts ten bytes later; the scalar may be that owner's immediate. -/
@[expose] def offset (index : Fin 4) : Nat :=
  match index.val with | 0 => 10 | 1 => 20 | 2 => 26 | _ => 33
@[expose] def raw (symbol : Dword) (index : Fin 4) : DwordArithmetic.Form :=
  match index.val with
  | 0 => .subtract 0 symbol
  | 1 => .negate 0
  | 2 => .sbbZero 0
  | _ => .complement 0
@[expose] def target (layout : Layout) (index : Fin 4) : Nat :=
  match index.val with | 0 | 1 => layout.scalar | _ => layout.mask
@[expose] def form (mode : Mode) (layout : Layout) (symbol : Dword) (index : Fin 4) :
    DwordArithmetic.Form :=
  DwordArithmetic.located mode (raw symbol index) (layout.start+offset index) (target layout index)
@[expose] def bytes (mode : Mode) (layout : Layout) (symbol : Dword) : List LittleEndian.Byte :=
  DwordArithmetic.encode (form mode layout symbol 0) ++
    DwordArithmetic.encode (form mode layout symbol 1) ++
    DwordArithmetic.encode (form mode layout symbol 2) ++
    DwordArithmetic.encode (form mode layout symbol 3)
@[expose] def Intact (mode : Mode) (layout : Layout) (symbol : Dword)
    (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory (layout.start+10) 29 = bytes mode layout symbol

structure Valid (mode : Mode) (layout : Layout) : Prop where
  codeFits : layout.start+39 < 2^(8*mode.wordBytes)
  scalarFits : layout.scalar+4 ≤ 2^(8*mode.wordBytes)
  maskFits : layout.mask+4 ≤ 2^(8*mode.wordBytes)
  separate : layout.scalar+4 ≤ layout.mask ∨ layout.mask+4 ≤ layout.scalar
  scalarOutside : layout.scalar+4 ≤ layout.start+10 ∨ layout.start+39 ≤ layout.scalar
  maskOutside : layout.mask+4 ≤ layout.start+10 ∨ layout.start+39 ≤ layout.mask
  ranges : ∀ index : Fin 4, mode = .x64 →
    Relocation.SignedDelta (layout.start+offset index+DwordArithmetic.length (raw 0 index))
      (target layout index)

theorem length (mode : Mode) (layout : Layout) (symbol : Dword) :
    (bytes mode layout symbol).length = 29 := by
  simp [bytes,form,raw,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.encode_length,DwordArithmetic.length]

theorem current_packet (mode : Mode) (layout : Layout) (symbol : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout symbol memory)
    (index : Fin 4) :
    ByteMemory.bytesAt memory (layout.start+offset index)
      (DwordArithmetic.encode (form mode layout symbol index)).length =
      DwordArithmetic.encode (form mode layout symbol index) := by
  have whole : ByteMemory.bytesAt memory (layout.start+10) (bytes mode layout symbol).length =
      bytes mode layout symbol := by simpa only [length,Intact] using intact
  fin_cases index
  · exact ByteWindow.packet memory (layout.start+10) []
      (DwordArithmetic.encode (form mode layout symbol 0))
      (DwordArithmetic.encode (form mode layout symbol 1) ++
        DwordArithmetic.encode (form mode layout symbol 2) ++
        DwordArithmetic.encode (form mode layout symbol 3))
      (by simpa [bytes,List.append_assoc] using whole)
  · have packet := ByteWindow.packet memory (layout.start+10)
      (DwordArithmetic.encode (form mode layout symbol 0))
      (DwordArithmetic.encode (form mode layout symbol 1))
      (DwordArithmetic.encode (form mode layout symbol 2) ++
        DwordArithmetic.encode (form mode layout symbol 3))
      (by simpa [bytes,List.append_assoc] using whole)
    simpa [form,raw,offset,DwordArithmetic.located,DwordArithmetic.relocate,
      DwordArithmetic.encode_length,DwordArithmetic.length,Nat.add_assoc] using packet
  · have packet := ByteWindow.packet memory (layout.start+10)
      (DwordArithmetic.encode (form mode layout symbol 0) ++
        DwordArithmetic.encode (form mode layout symbol 1))
      (DwordArithmetic.encode (form mode layout symbol 2))
      (DwordArithmetic.encode (form mode layout symbol 3))
      (by simpa [bytes,List.append_assoc] using whole)
    simpa [List.length_append,form,raw,offset,DwordArithmetic.located,
      DwordArithmetic.relocate,DwordArithmetic.encode_length,DwordArithmetic.length,
      Nat.add_assoc] using packet
  · have packet := ByteWindow.packet memory (layout.start+10)
      (DwordArithmetic.encode (form mode layout symbol 0) ++
        DwordArithmetic.encode (form mode layout symbol 1) ++
        DwordArithmetic.encode (form mode layout symbol 2))
      (DwordArithmetic.encode (form mode layout symbol 3)) []
      (by simpa [bytes,List.append_assoc] using whole)
    simpa [List.length_append,form,raw,offset,DwordArithmetic.located,
      DwordArithmetic.relocate,DwordArithmetic.encode_length,DwordArithmetic.length,
      Nat.add_assoc] using packet

theorem intact_put (mode : Mode) (layout : Layout) (symbol : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout symbol memory)
    (field : Nat) (value : Dword)
    (outside : field+4 ≤ layout.start+10 ∨ layout.start+39 ≤ field) :
    Intact mode layout symbol (DwordCode.put memory field value) := by
  rw [Intact,DwordCode.put,ByteMemory.bytes_at_frame]
  · exact intact
  · intro index
    have bound := index.isLt
    simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
    rcases outside with before | after <;> omega

theorem located_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (index : Fin 4) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+offset index)) :
    DwordArithmetic.execute mode (form mode layout symbol index) state =
      { state with
        pc := Arithmetic.encodeNat mode
          (layout.start+offset index+DwordArithmetic.length (raw symbol index))
        carry := DwordArithmetic.flag (raw symbol index)
          (DwordCode.get state.memory (target layout index)) state.carry
        memory := DwordCode.put state.memory (target layout index)
          (DwordArithmetic.result (raw symbol index)
            (DwordCode.get state.memory (target layout index)) state.carry) } := by
  apply DwordArithmetic.located_effect
  · fin_cases index <;> rfl
  · exact entry
  · have range := valid.ranges index
    fin_cases index <;> exact range
  · have scalar := valid.scalarFits
    have mask := valid.maskFits
    fin_cases index <;> simp only [target] <;> omega

theorem intact_execute (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (index : Fin 4) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+offset index))
    (intact : Intact mode layout symbol state.memory) :
    Intact mode layout symbol (DwordArithmetic.execute mode (form mode layout symbol index) state).memory := by
  rw [located_effect mode layout valid symbol index state entry]
  apply intact_put mode layout symbol state.memory intact
  fin_cases index
  · exact valid.scalarOutside
  · exact valid.scalarOutside
  · exact valid.maskOutside
  · exact valid.maskOutside

@[expose] def subState (mode : Mode) (layout : Layout) (symbol : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  DwordArithmetic.execute mode (form mode layout symbol 0) state
@[expose] def negState (mode : Mode) (layout : Layout) (symbol : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  DwordArithmetic.execute mode (form mode layout symbol 1) (subState mode layout symbol state)
@[expose] def sbbState (mode : Mode) (layout : Layout) (symbol : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  DwordArithmetic.execute mode (form mode layout symbol 2) (negState mode layout symbol state)
@[expose] def finish (mode : Mode) (layout : Layout) (symbol : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  DwordArithmetic.execute mode (form mode layout symbol 3) (sbbState mode layout symbol state)
@[expose] def program (mode : Mode) (layout : Layout) (symbol : Dword) :
    List (MixedDword.Form mode) :=
  [.arithmetic (form mode layout symbol 0),.arithmetic (form mode layout symbol 1),
   .arithmetic (form mode layout symbol 2),.arithmetic (form mode layout symbol 3)]

theorem sub_pc (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10)) :
    (subState mode layout symbol state).pc = Arithmetic.encodeNat mode (layout.start+20) := by
  rw [subState,located_effect mode layout valid symbol 0 state entry]
  simp [offset,raw,DwordArithmetic.length,Nat.add_assoc]

theorem neg_pc (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10)) :
    (negState mode layout symbol state).pc = Arithmetic.encodeNat mode (layout.start+26) := by
  rw [negState,located_effect mode layout valid symbol 1 _
    (sub_pc mode layout valid symbol state entry)]
  simp [offset,raw,DwordArithmetic.length,Nat.add_assoc]

theorem sbb_pc (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10)) :
    (sbbState mode layout symbol state).pc = Arithmetic.encodeNat mode (layout.start+33) := by
  rw [sbbState,located_effect mode layout valid symbol 2 _
    (neg_pc mode layout valid symbol state entry)]
  simp [offset,raw,DwordArithmetic.length,Nat.add_assoc]

theorem finish_pc (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10)) :
    (finish mode layout symbol state).pc = Arithmetic.encodeNat mode (layout.start+39) := by
  rw [finish,located_effect mode layout valid symbol 3 _
    (sbb_pc mode layout valid symbol state entry)]
  simp [offset,raw,DwordArithmetic.length,Nat.add_assoc]

theorem sub_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (intact : Intact mode layout symbol state.memory) :
    Intact mode layout symbol (subState mode layout symbol state).memory :=
  intact_execute mode layout valid symbol 0 state entry intact

theorem neg_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (intact : Intact mode layout symbol state.memory) :
    Intact mode layout symbol (negState mode layout symbol state).memory :=
  intact_execute mode layout valid symbol 1 _ (sub_pc mode layout valid symbol state entry)
    (sub_intact mode layout valid symbol state entry intact)

theorem sbb_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (intact : Intact mode layout symbol state.memory) :
    Intact mode layout symbol (sbbState mode layout symbol state).memory :=
  intact_execute mode layout valid symbol 2 _ (neg_pc mode layout valid symbol state entry)
    (neg_intact mode layout valid symbol state entry intact)

theorem finish_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (intact : Intact mode layout symbol state.memory) :
    Intact mode layout symbol (finish mode layout symbol state).memory :=
  intact_execute mode layout valid symbol 3 _ (sbb_pc mode layout valid symbol state entry)
    (sbb_intact mode layout valid symbol state entry intact)

theorem fetched (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (index : Fin 4) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+offset index))
    (intact : Intact mode layout symbol state.memory) :
    MixedDword.fetch mode state.memory state.pc.toNat =
      some (.arithmetic (form mode layout symbol index)) := by
  have fits : layout.start+offset index < 2^(8*mode.wordBytes) := by
    have bound := valid.codeFits
    fin_cases index <;> simp only [offset] <;> omega
  rw [entry,Arithmetic.encode_nat_toNat mode _ fits]
  exact MixedDword.arithmetic_encoding mode state.memory _ _
    (current_packet mode layout symbol state.memory intact index)

/-- The actual four current-byte fetches depend only on the initial tail
image and static address/separation facts. The preceding reset may be remote. -/
theorem trace (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (intact : Intact mode layout symbol state.memory) :
    MixedDword.Trace mode state (program mode layout symbol) (finish mode layout symbol state) := by
  have a := fetched mode layout valid symbol 0 state entry intact
  have b := fetched mode layout valid symbol 1 _ (sub_pc mode layout valid symbol state entry)
    (sub_intact mode layout valid symbol state entry intact)
  have c := fetched mode layout valid symbol 2 _ (neg_pc mode layout valid symbol state entry)
    (neg_intact mode layout valid symbol state entry intact)
  have d := fetched mode layout valid symbol 3 _ (sbb_pc mode layout valid symbol state entry)
    (sbb_intact mode layout valid symbol state entry intact)
  exact .step a (.step b (.step c (.step d (.nil _))))

@[expose] def mismatch (candidate symbol : Dword) : Bool := decide (candidate-symbol ≠ 0)

theorem sub_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (candidate symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (value : DwordCode.get state.memory layout.scalar = candidate) :
    subState mode layout symbol state =
      { state with
        pc := Arithmetic.encodeNat mode (layout.start+20)
        carry := decide (candidate.toNat < symbol.toNat)
        memory := DwordCode.put state.memory layout.scalar (candidate-symbol) } := by
  rw [subState,located_effect mode layout valid symbol 0 state entry]
  simp [raw,target,offset,DwordArithmetic.flag,DwordArithmetic.result,
    DwordArithmetic.length,value,Nat.add_assoc]

theorem neg_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (candidate symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (value : DwordCode.get state.memory layout.scalar = candidate) :
    negState mode layout symbol state =
      { state with
        pc := Arithmetic.encodeNat mode (layout.start+26)
        carry := mismatch candidate symbol
        memory := DwordCode.put state.memory layout.scalar (-(candidate-symbol)) } := by
  rw [negState,located_effect mode layout valid symbol 1 _
    (sub_pc mode layout valid symbol state entry),sub_effect mode layout valid candidate symbol state entry value]
  simp [raw,target,offset,DwordArithmetic.flag,DwordArithmetic.result,
    DwordArithmetic.length,mismatch,DwordCode.get_put,DwordCode.put_overwrite,Nat.add_assoc]

theorem mask_apart (mode : Mode) (layout : Layout) (valid : Valid mode layout) :
    ∀ index : Fin 4, ¬ByteMemory.Inside layout.scalar 4 (layout.mask+index.val) := by
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases valid.separate with before | after <;> omega

theorem mask_after_neg (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (candidate symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (value : DwordCode.get state.memory layout.scalar = candidate)
    (zero : DwordCode.get state.memory layout.mask = 0) :
    DwordCode.get (negState mode layout symbol state).memory layout.mask = 0 := by
  rw [neg_effect mode layout valid candidate symbol state entry value,
    DwordCode.get_frame _ _ _ _ (mask_apart mode layout valid)]
  exact zero

theorem sbb_result (carry : Bool) :
    DwordArithmetic.result (.sbbZero 0) 0 carry = BranchAlgebra.mask carry := by
  cases carry <;> rfl

theorem sbb_flag (carry : Bool) :
    DwordArithmetic.flag (.sbbZero 0) 0 carry = carry := by
  cases carry <;> decide

theorem sbb_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (candidate symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (value : DwordCode.get state.memory layout.scalar = candidate)
    (zero : DwordCode.get state.memory layout.mask = 0) :
    sbbState mode layout symbol state =
      { negState mode layout symbol state with
        pc := Arithmetic.encodeNat mode (layout.start+33)
        carry := mismatch candidate symbol
        memory := DwordCode.put (negState mode layout symbol state).memory layout.mask
          (BranchAlgebra.mask (mismatch candidate symbol)) } := by
  have step := located_effect mode layout valid symbol 2 (negState mode layout symbol state)
    (neg_pc mode layout valid symbol state entry)
  simp only [show target layout (2 : Fin 4) = layout.mask from rfl] at step
  have carry : (negState mode layout symbol state).carry = mismatch candidate symbol := by
    rw [neg_effect mode layout valid candidate symbol state entry value]
  rw [mask_after_neg mode layout valid candidate symbol state entry value zero,carry] at step
  change sbbState mode layout symbol state = _ at step
  simp only [show raw symbol (2 : Fin 4) = .sbbZero 0 from rfl,
    show offset (2 : Fin 4) = 26 from rfl] at step
  rw [sbb_result,sbb_flag] at step
  simpa [DwordArithmetic.length,Nat.add_assoc] using step

theorem mask_after_sbb (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (candidate symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (value : DwordCode.get state.memory layout.scalar = candidate)
    (zero : DwordCode.get state.memory layout.mask = 0) :
    DwordCode.get (sbbState mode layout symbol state).memory layout.mask =
      BranchAlgebra.mask (mismatch candidate symbol) := by
  rw [sbb_effect mode layout valid candidate symbol state entry value zero,DwordCode.get_put]

theorem effect (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (candidate symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (value : DwordCode.get state.memory layout.scalar = candidate)
    (zero : DwordCode.get state.memory layout.mask = 0) :
    finish mode layout symbol state =
      { state with
        pc := Arithmetic.encodeNat mode (layout.start+39)
        carry := mismatch candidate symbol
        memory := DwordCode.put
          (DwordCode.put state.memory layout.scalar (-(candidate-symbol))) layout.mask
          (BranchAlgebra.mask (!(mismatch candidate symbol))) } := by
  have step := located_effect mode layout valid symbol 3 (sbbState mode layout symbol state)
    (sbb_pc mode layout valid symbol state entry)
  simp only [show target layout (3 : Fin 4) = layout.mask from rfl] at step
  have carry : (sbbState mode layout symbol state).carry = mismatch candidate symbol := by
    rw [sbb_effect mode layout valid candidate symbol state entry value zero]
  rw [mask_after_sbb mode layout valid candidate symbol state entry value zero,carry] at step
  change finish mode layout symbol state = _ at step
  rw [sbb_effect mode layout valid candidate symbol state entry value zero,
    neg_effect mode layout valid candidate symbol state entry value] at step
  simpa [raw,offset,DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length,
    BranchAlgebra.complement_mask,DwordCode.put_overwrite,Nat.add_assoc] using step

/-- The comparison tail has a complete live-byte trace, exact equality-mask
effect and retained packets, with the scalar in an earlier owner and the mask
in any statically valid later field. -/
theorem correct (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (candidate symbol : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (layout.start+10))
    (intact : Intact mode layout symbol state.memory)
    (value : DwordCode.get state.memory layout.scalar = candidate)
    (zero : DwordCode.get state.memory layout.mask = 0) :
    MixedDword.Trace mode state (program mode layout symbol) (finish mode layout symbol state) ∧
    finish mode layout symbol state =
      { state with
        pc := Arithmetic.encodeNat mode (layout.start+39)
        carry := mismatch candidate symbol
        memory := DwordCode.put
          (DwordCode.put state.memory layout.scalar (-(candidate-symbol))) layout.mask
          (BranchAlgebra.mask (!(mismatch candidate symbol))) } ∧
    Intact mode layout symbol (finish mode layout symbol state).memory :=
  ⟨trace mode layout valid symbol state entry intact,
    effect mode layout valid candidate symbol state entry value zero,
    finish_intact mode layout valid symbol state entry intact⟩

end SmcTuring.Appendix.DwordComparisonTail
