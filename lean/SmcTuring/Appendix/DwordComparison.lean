module
public import SmcTuring.Native.DwordArithmetic
public import SmcTuring.Appendix.BranchAlgebra
public import SmcTuring.Native.DwordLayout
public import SmcTuring.Appendix.ByteImage
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

public section
namespace SmcTuring.Appendix.DwordComparison
open Native Native.DwordCode
abbrev Dword := BitVec 32
abbrev ArithForm := DwordArithmetic.Form

structure Layout where
  start : Nat
  scalar : Nat
  mask : Nat
@[expose] def offset (index : Fin 5) : Nat :=
  match index.val with | 0 => 0 | 1 => 10 | 2 => 20 | 3 => 26 | _ => 33
@[expose] def target (layout : Layout) (index : Fin 5) : Nat :=
  match index.val with | 1 | 2 => layout.scalar | _ => layout.mask
@[expose] def raw (symbol : Dword) (index : Fin 5) : ArithForm :=
  match index.val with
  | 0 => .store 0 0
  | 1 => .subtract 0 symbol
  | 2 => .negate 0
  | 3 => .sbbZero 0
  | _ => .complement 0
@[expose] def form (mode : Mode) (layout : Layout) (symbol : Dword) (index : Fin 5) : ArithForm :=
  DwordArithmetic.located mode (raw symbol index) (layout.start+offset index) (target layout index)
@[expose] def bytes (mode : Mode) (layout : Layout) (symbol : Dword) : List LittleEndian.Byte :=
  DwordArithmetic.encode (form mode layout symbol 0) ++
  DwordArithmetic.encode (form mode layout symbol 1) ++
  DwordArithmetic.encode (form mode layout symbol 2) ++
  DwordArithmetic.encode (form mode layout symbol 3) ++
  DwordArithmetic.encode (form mode layout symbol 4)
@[expose] def image (mode : Mode) (layout : Layout) (symbol : Dword) (memory : ByteMemory.Memory) :
    ByteMemory.Memory := ByteMemory.putBytes memory layout.start (bytes mode layout symbol)
@[expose] def Intact (mode : Mode) (layout : Layout) (symbol : Dword) (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory layout.start 39 = bytes mode layout symbol

structure Valid (mode : Mode) (layout : Layout) : Prop where
  codeFits : layout.start+39 < 2^(8*mode.wordBytes)
  scalarFits : layout.scalar+4 ≤ 2^(8*mode.wordBytes)
  maskFits : layout.mask+4 ≤ 2^(8*mode.wordBytes)
  separate : layout.scalar+4 ≤ layout.mask ∨ layout.mask+4 ≤ layout.scalar
  scalarOutside : layout.scalar+4 ≤ layout.start ∨ layout.start+39 ≤ layout.scalar
  maskOutside : layout.mask+4 ≤ layout.start ∨ layout.start+39 ≤ layout.mask
  ranges : ∀ index : Fin 5, mode = .x64 →
    Relocation.SignedDelta (layout.start+offset index+DwordArithmetic.length (raw 0 index)) (target layout index)

theorem length (mode : Mode) (layout : Layout) (symbol : Dword) : (bytes mode layout symbol).length = 39 := by
  simp [bytes,form,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.encode_length,raw,DwordArithmetic.length]

theorem initially_intact (mode : Mode) (layout : Layout) (symbol : Dword) (memory : ByteMemory.Memory) :
    Intact mode layout symbol (image mode layout symbol memory) := by
  rw [Intact,←length mode layout symbol]
  exact ByteMemory.bytes_at_put _ _ _

theorem packet_window (memory : ByteMemory.Memory) (start : Nat) (leading packet trailing : List LittleEndian.Byte)
    (current : ByteMemory.bytesAt memory start (leading++packet++trailing).length = leading++packet++trailing) :
    ByteMemory.bytesAt memory (start+leading.length) packet.length = packet := by
  have taken := Fetch.bytes_at_take memory start (leading++packet++trailing).length
    (leading.length+packet.length) (by simp)
  rw [current] at taken
  have trimmed : (leading++packet++trailing).take (leading.length+packet.length) = leading++packet := by
    rw [←List.length_append,List.take_append_length]
  rw [trimmed] at taken
  have dropped := congrArg (List.drop leading.length) taken
  rw [ByteImage.bytes_at_drop] at dropped
  simpa only [List.drop_append_length] using dropped.symm

theorem current_packet (mode : Mode) (layout : Layout) (symbol : Dword) (memory : ByteMemory.Memory)
    (intact : Intact mode layout symbol memory) (index : Fin 5) :
    ByteMemory.bytesAt memory (layout.start+offset index) (DwordArithmetic.encode (form mode layout symbol index)).length =
      DwordArithmetic.encode (form mode layout symbol index) := by
  have current : ByteMemory.bytesAt memory layout.start (bytes mode layout symbol).length =
      bytes mode layout symbol := by simpa only [length,Intact] using intact
  fin_cases index
  · exact packet_window memory layout.start []
      (DwordArithmetic.encode (form mode layout symbol 0))
      (DwordArithmetic.encode (form mode layout symbol 1) ++ DwordArithmetic.encode (form mode layout symbol 2) ++
       DwordArithmetic.encode (form mode layout symbol 3) ++ DwordArithmetic.encode (form mode layout symbol 4))
      (by simpa [bytes,List.append_assoc] using current)
  · have found := packet_window memory layout.start
      (DwordArithmetic.encode (form mode layout symbol 0))
      (DwordArithmetic.encode (form mode layout symbol 1))
      (DwordArithmetic.encode (form mode layout symbol 2) ++
       DwordArithmetic.encode (form mode layout symbol 3) ++ DwordArithmetic.encode (form mode layout symbol 4))
      (by simpa [bytes,List.append_assoc] using current)
    simpa [form,DwordArithmetic.located,DwordArithmetic.encode_length,DwordArithmetic.relocate_length,
      raw,DwordArithmetic.length,offset,DwordArithmetic.relocate] using found
  · have found := packet_window memory layout.start
      (DwordArithmetic.encode (form mode layout symbol 0) ++ DwordArithmetic.encode (form mode layout symbol 1))
      (DwordArithmetic.encode (form mode layout symbol 2))
      (DwordArithmetic.encode (form mode layout symbol 3) ++ DwordArithmetic.encode (form mode layout symbol 4))
      (by simpa [bytes,List.append_assoc] using current)
    simpa [form,DwordArithmetic.located,DwordArithmetic.encode_length,DwordArithmetic.relocate_length,
      raw,DwordArithmetic.length,offset,DwordArithmetic.relocate] using found
  · have found := packet_window memory layout.start
      (DwordArithmetic.encode (form mode layout symbol 0) ++ DwordArithmetic.encode (form mode layout symbol 1) ++
       DwordArithmetic.encode (form mode layout symbol 2))
      (DwordArithmetic.encode (form mode layout symbol 3))
      (DwordArithmetic.encode (form mode layout symbol 4))
      (by simpa [bytes,List.append_assoc] using current)
    simpa [form,DwordArithmetic.located,DwordArithmetic.encode_length,DwordArithmetic.relocate_length,
      raw,DwordArithmetic.length,offset,DwordArithmetic.relocate] using found
  · have found := packet_window memory layout.start
      (DwordArithmetic.encode (form mode layout symbol 0) ++ DwordArithmetic.encode (form mode layout symbol 1) ++
       DwordArithmetic.encode (form mode layout symbol 2) ++ DwordArithmetic.encode (form mode layout symbol 3))
      (DwordArithmetic.encode (form mode layout symbol 4)) []
      (by simpa [bytes,List.append_assoc] using current)
    simpa [form,DwordArithmetic.located,DwordArithmetic.encode_length,DwordArithmetic.relocate_length,
      raw,DwordArithmetic.length,offset,DwordArithmetic.relocate] using found

theorem intact_put (mode : Mode) (layout : Layout) (symbol : Dword) (memory : ByteMemory.Memory)
    (intact : Intact mode layout symbol memory) (field : Nat) (value : Dword)
    (outside : field+4 ≤ layout.start ∨ layout.start+39 ≤ field) :
    Intact mode layout symbol (put memory field value) := by
  rw [Intact,put,ByteMemory.bytes_at_frame]
  · exact intact
  · intro index
    have bound := index.isLt
    simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
    rcases outside with before | after <;> omega

theorem scalar_apart (mode : Mode) (layout : Layout) (valid : Valid mode layout) :
    ∀ index : Fin 4, ¬ByteMemory.Inside layout.mask 4 (layout.scalar+index.val) := by
  intro index
  have bound := index.isLt
  have apart := valid.separate
  unfold ByteMemory.Inside
  omega
theorem mask_apart (mode : Mode) (layout : Layout) (valid : Valid mode layout) :
    ∀ index : Fin 4, ¬ByteMemory.Inside layout.scalar 4 (layout.mask+index.val) := by
  intro index
  have bound := index.isLt
  have apart := valid.separate
  unfold ByteMemory.Inside
  omega

theorem located_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (index : Fin 5) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode (layout.start+offset index)) :
    DwordArithmetic.execute mode (form mode layout symbol index) state =
      { state with
        pc := Arithmetic.encodeNat mode (layout.start+offset index+DwordArithmetic.length (raw symbol index))
        carry := DwordArithmetic.flag (raw symbol index) (get state.memory (target layout index)) state.carry
        memory := put state.memory (target layout index)
          (DwordArithmetic.result (raw symbol index) (get state.memory (target layout index)) state.carry) } := by
  apply DwordArithmetic.located_effect
  · fin_cases index <;> rfl
  · exact location
  · have range := valid.ranges index
    fin_cases index <;> exact range
  · have sf := valid.scalarFits
    have mf := valid.maskFits
    fin_cases index <;> simp only [target] <;> omega

@[expose] def candidate {mode : Mode} (layout : Layout) (state : Execution.State mode) : Dword := get state.memory layout.scalar
@[expose] def mismatch {mode : Mode} (layout : Layout) (state : Execution.State mode) (symbol : Dword) : Bool :=
  decide (candidate layout state - symbol ≠ 0#32)
@[expose] def reset (mode : Mode) (layout : Layout) (state : Execution.State mode) : Execution.State mode :=
  { state with
    pc := Arithmetic.encodeNat mode (layout.start+10)
    memory := put state.memory layout.mask 0 }
@[expose] def subtracted (mode : Mode) (layout : Layout) (symbol : Dword) (state : Execution.State mode) :
    Execution.State mode :=
  { state with
    pc := Arithmetic.encodeNat mode (layout.start+20)
    carry := decide ((candidate layout state).toNat < symbol.toNat)
    memory := put (reset mode layout state).memory layout.scalar (candidate layout state-symbol) }
@[expose] def negated (mode : Mode) (layout : Layout) (symbol : Dword) (state : Execution.State mode) :
    Execution.State mode :=
  { state with
    pc := Arithmetic.encodeNat mode (layout.start+26)
    carry := mismatch layout state symbol
    memory := put (reset mode layout state).memory layout.scalar (-(candidate layout state-symbol)) }
@[expose] def borrowed (mode : Mode) (layout : Layout) (symbol : Dword) (state : Execution.State mode) :
    Execution.State mode :=
  { state with
    pc := Arithmetic.encodeNat mode (layout.start+33)
    carry := mismatch layout state symbol
    memory := put (negated mode layout symbol state).memory layout.mask
      (BranchAlgebra.mask (mismatch layout state symbol)) }
@[expose] def finish (mode : Mode) (layout : Layout) (symbol : Dword) (state : Execution.State mode) :
    Execution.State mode :=
  { state with
    pc := Arithmetic.encodeNat mode (layout.start+39)
    carry := mismatch layout state symbol
    memory := put (negated mode layout symbol state).memory layout.mask
      (BranchAlgebra.mask (!(mismatch layout state symbol))) }

theorem reset_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    DwordArithmetic.execute mode (form mode layout symbol 0) state = reset mode layout state := by
  rw [located_effect mode layout valid symbol 0 state (by simpa [offset] using entry)]
  rfl

theorem subtracted_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) :
    DwordArithmetic.execute mode (form mode layout symbol 1) (reset mode layout state) =
      subtracted mode layout symbol state := by
  rw [located_effect mode layout valid symbol 1 _ rfl]
  simp [raw,target,offset,DwordArithmetic.length,DwordArithmetic.flag,DwordArithmetic.result,
    reset,subtracted,candidate,Nat.add_assoc,get_frame _ _ _ _ (scalar_apart mode layout valid)]
  rfl

theorem negated_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) :
    DwordArithmetic.execute mode (form mode layout symbol 2) (subtracted mode layout symbol state) =
      negated mode layout symbol state := by
  rw [located_effect mode layout valid symbol 2 _ rfl]
  simp [raw,target,offset,DwordArithmetic.length,DwordArithmetic.flag,DwordArithmetic.result,
    subtracted,negated,mismatch,Nat.add_assoc,put_overwrite,get_put]

theorem borrowed_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) :
    DwordArithmetic.execute mode (form mode layout symbol 3) (negated mode layout symbol state) =
      borrowed mode layout symbol state := by
  rw [located_effect mode layout valid symbol 3 _ rfl]
  have zero : get (negated mode layout symbol state).memory layout.mask = 0 := by
    simp [negated,reset,get_frame _ _ _ _ (mask_apart mode layout valid),get_put]
  rw [show target layout 3 = layout.mask from rfl,zero]
  simp [raw,offset,DwordArithmetic.length,DwordArithmetic.flag,DwordArithmetic.result,
    negated,borrowed,Nat.add_assoc]
  by_cases h : mismatch layout state symbol = true
  · simp [h,BranchAlgebra.mask]
  · have hf : mismatch layout state symbol = false := Bool.eq_false_iff.mpr h
    simp [hf,BranchAlgebra.mask]

theorem finish_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) :
    DwordArithmetic.execute mode (form mode layout symbol 4) (borrowed mode layout symbol state) =
      finish mode layout symbol state := by
  rw [located_effect mode layout valid symbol 4 _ rfl]
  simp [raw,target,offset,DwordArithmetic.length,DwordArithmetic.flag,DwordArithmetic.result,
    borrowed,finish,Nat.add_assoc,get_put,put_overwrite,BranchAlgebra.complement_mask]

theorem intermediate_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (intact : Intact mode layout symbol state.memory) :
    Intact mode layout symbol (reset mode layout state).memory ∧
    Intact mode layout symbol (subtracted mode layout symbol state).memory ∧
    Intact mode layout symbol (negated mode layout symbol state).memory ∧
    Intact mode layout symbol (borrowed mode layout symbol state).memory ∧
    Intact mode layout symbol (finish mode layout symbol state).memory := by
  have r := intact_put mode layout symbol state.memory intact layout.mask 0 valid.maskOutside
  have s := intact_put mode layout symbol _ r layout.scalar (candidate layout state-symbol) valid.scalarOutside
  have n := intact_put mode layout symbol _ r layout.scalar (-(candidate layout state-symbol)) valid.scalarOutside
  have b := intact_put mode layout symbol _ n layout.mask (BranchAlgebra.mask (mismatch layout state symbol)) valid.maskOutside
  have f := intact_put mode layout symbol _ n layout.mask (BranchAlgebra.mask (!(mismatch layout state symbol))) valid.maskOutside
  exact ⟨r,s,n,b,f⟩

/-- Every future fetch is derived from the same initial current image after
the preceding scalar/mask stores. No future-fetch premise occurs here. -/
theorem trace (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout symbol state.memory) :
    DwordArithmetic.Trace mode state
      [form mode layout symbol 0,form mode layout symbol 1,form mode layout symbol 2,
       form mode layout symbol 3,form mode layout symbol 4] (finish mode layout symbol state) := by
  have images := intermediate_intact mode layout valid symbol state intact
  have fetched (index : Fin 5) (s : Execution.State mode)
      (location : s.pc = Arithmetic.encodeNat mode (layout.start+offset index))
      (current : Intact mode layout symbol s.memory) :
      DwordArithmetic.fetch s.memory s.pc.toNat = some (form mode layout symbol index) := by
    rw [location,Arithmetic.encode_nat_toNat mode _ (by
      have high := valid.codeFits
      fin_cases index <;> simp only [offset] <;> omega)]
    exact DwordArithmetic.fetch_encoding _ _ _ (current_packet mode layout symbol _ current index)
  apply DwordArithmetic.Trace.step (fetched 0 state (by simpa [offset] using entry) intact)
  rw [reset_effect mode layout valid symbol state entry]
  apply DwordArithmetic.Trace.step (fetched 1 _ rfl images.1)
  rw [subtracted_effect mode layout valid symbol state]
  apply DwordArithmetic.Trace.step (fetched 2 _ rfl images.2.1)
  rw [negated_effect mode layout valid symbol state]
  apply DwordArithmetic.Trace.step (fetched 3 _ rfl images.2.2.1)
  rw [borrowed_effect mode layout valid symbol state]
  apply DwordArithmetic.Trace.step (fetched 4 _ rfl images.2.2.2.1)
  rw [finish_effect mode layout valid symbol state]
  exact DwordArithmetic.Trace.nil _

theorem difference_zero (candidate symbol : Dword) : candidate-symbol=0#32 ↔ candidate=symbol := by
  constructor
  · intro equal
    have same := congrArg (fun v : Dword => v+symbol) equal
    simpa only [BitVec.sub_add_cancel,BitVec.zero_add] using same
  · intro same
    simp only [same,BitVec.sub_self]

theorem mask_value (mode : Mode) (layout : Layout) (symbol : Dword) (state : Execution.State mode) :
    get (finish mode layout symbol state).memory layout.mask =
      if candidate layout state = symbol then BitVec.allOnes 32 else 0 := by
  simp only [finish,get_put,mismatch]
  by_cases same : candidate layout state = symbol
  · simp [same,BranchAlgebra.mask]
  · have different : candidate layout state-symbol ≠ 0#32 := fun equal => same ((difference_zero _ _).mp equal)
    simp [same,different,BranchAlgebra.mask]

theorem memory_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) :
    (finish mode layout symbol state).memory =
      put (put state.memory layout.scalar (-(candidate layout state-symbol))) layout.mask
        (if candidate layout state = symbol then BitVec.allOnes 32 else 0) := by
  have mask : BranchAlgebra.mask (!(mismatch layout state symbol)) =
      if candidate layout state = symbol then BitVec.allOnes 32 else 0 := by
    by_cases same : candidate layout state = symbol
    · simp [mismatch,same,BranchAlgebra.mask]
    · have different : candidate layout state-symbol ≠ 0#32 := fun equal => same ((difference_zero _ _).mp equal)
      simp [mismatch,same,different,BranchAlgebra.mask]
  change put (put (put state.memory layout.mask 0) layout.scalar (-(candidate layout state-symbol)))
    layout.mask _ = _
  rw [put_commute state.memory layout.mask layout.scalar 0 _ (mask_apart mode layout valid),
      put_overwrite,mask]

theorem frame (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (position : Nat)
    (scalarOutside : ¬ByteMemory.Inside layout.scalar 4 position)
    (maskOutside : ¬ByteMemory.Inside layout.mask 4 position) :
    (finish mode layout symbol state).memory position = state.memory position := by
  rw [memory_effect mode layout valid symbol state]
  rw [put,ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using maskOutside)]
  rw [put,ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using scalarOutside)]

/-- Architectural stores remain four nonempty code-word writes plus the
mask initialization; unchanged bytes do not remove write events. -/
theorem owned_destinations (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (owned : Nat → Prop) (scalarOwned : owned layout.scalar) (maskOwned : owned layout.mask) :
    owned (DwordArithmetic.address mode (form mode layout symbol 0) state).toNat ∧
    owned (DwordArithmetic.address mode (form mode layout symbol 1) (reset mode layout state)).toNat ∧
    owned (DwordArithmetic.address mode (form mode layout symbol 2) (subtracted mode layout symbol state)).toNat ∧
    owned (DwordArithmetic.address mode (form mode layout symbol 3) (negated mode layout symbol state)).toNat ∧
    owned (DwordArithmetic.address mode (form mode layout symbol 4) (borrowed mode layout symbol state)).toNat := by
  have hits (index : Fin 5) (s : Execution.State mode)
      (location : s.pc = Arithmetic.encodeNat mode (layout.start+offset index)) :
      (DwordArithmetic.address mode (form mode layout symbol index) s).toNat = target layout index := by
    unfold form
    rw [DwordArithmetic.located_address mode (raw symbol index) (layout.start+offset index) (target layout index) s (by fin_cases index <;> rfl) location
      (by have ranges := valid.ranges index; fin_cases index <;> exact ranges)]
    apply Arithmetic.encode_nat_toNat
    have sf := valid.scalarFits
    have mf := valid.maskFits
    fin_cases index <;> simp only [target] <;> omega
  rw [hits 0 state (by simpa [offset] using entry),hits 1 _ rfl,hits 2 _ rfl,hits 3 _ rfl,hits 4 _ rfl]
  exact ⟨maskOwned,scalarOwned,scalarOwned,maskOwned,maskOwned⟩

theorem correct (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout symbol state.memory) :
    DwordArithmetic.Trace mode state
      [form mode layout symbol 0,form mode layout symbol 1,form mode layout symbol 2,
       form mode layout symbol 3,form mode layout symbol 4] (finish mode layout symbol state) ∧
    get (finish mode layout symbol state).memory layout.mask =
      (if candidate layout state = symbol then BitVec.allOnes 32 else 0) ∧
    (finish mode layout symbol state).pc = Arithmetic.encodeNat mode (layout.start+39) ∧
    (finish mode layout symbol state).accumulator = state.accumulator ∧
    (finish mode layout symbol state).stack = state.stack ∧
    (finish mode layout symbol state).carry = decide (candidate layout state ≠ symbol) ∧
    Intact mode layout symbol (finish mode layout symbol state).memory := by
  refine ⟨trace mode layout valid symbol state entry intact,mask_value mode layout symbol state,
    rfl,rfl,rfl,?_,(intermediate_intact mode layout valid symbol state intact).2.2.2.2⟩
  change decide (candidate layout state-symbol ≠ 0#32) = decide (candidate layout state ≠ symbol)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr (difference_zero _ _)

theorem original_correct (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (backing : ByteMemory.Memory)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (initial : state.memory = image mode layout symbol backing) :
    DwordArithmetic.Trace mode state
      [form mode layout symbol 0,form mode layout symbol 1,form mode layout symbol 2,
       form mode layout symbol 3,form mode layout symbol 4] (finish mode layout symbol state) := by
  apply trace mode layout valid symbol state entry
  rw [initial]
  exact initially_intact mode layout symbol backing

theorem pure (mode : Mode) (layout : Layout) (valid : Valid mode layout) (symbol : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (owned : Nat → Prop) (scalarOwned : owned layout.scalar) (maskOwned : owned layout.mask) :
    DwordArithmetic.OwnedRun mode owned
      [form mode layout symbol 0,form mode layout symbol 1,form mode layout symbol 2,
       form mode layout symbol 3,form mode layout symbol 4] state := by
  simp only [DwordArithmetic.OwnedRun]
  simp only [reset_effect mode layout valid symbol state entry,subtracted_effect mode layout valid symbol state,
    negated_effect mode layout valid symbol state,borrowed_effect mode layout valid symbol state]
  simpa only [and_true] using owned_destinations mode layout valid symbol state entry owned scalarOwned maskOwned

@[expose] def checks (mode : Mode) (layout : Layout) : List Bool :=
  [decide (layout.start+39 < 2^(8*mode.wordBytes)),
   decide (layout.scalar+4 ≤ 2^(8*mode.wordBytes)),
   decide (layout.mask+4 ≤ 2^(8*mode.wordBytes)),
   decide (layout.scalar+4 ≤ layout.mask ∨ layout.mask+4 ≤ layout.scalar),
   decide (layout.scalar+4 ≤ layout.start ∨ layout.start+39 ≤ layout.scalar),
   decide (layout.mask+4 ≤ layout.start ∨ layout.start+39 ≤ layout.mask),
   DwordLayout.reachable mode (layout.start+10) layout.mask,
   DwordLayout.reachable mode (layout.start+20) layout.scalar,
   DwordLayout.reachable mode (layout.start+26) layout.scalar,
   DwordLayout.reachable mode (layout.start+33) layout.mask,
   DwordLayout.reachable mode (layout.start+39) layout.mask]

theorem checks_valid (mode : Mode) (layout : Layout) :
    (checks mode layout).all id = true ↔ Valid mode layout := by
  simp only [checks,List.all_cons,List.all_nil,id_eq,Bool.and_eq_true,and_true,decide_eq_true_eq,DwordLayout.reachable_iff]
  constructor
  · rintro ⟨code,sf,mf,sep,so,mo,r0,r1,r2,r3,r4⟩
    refine ⟨code,sf,mf,sep,so,mo,?_⟩
    intro index
    fin_cases index <;> simpa [offset,target,raw,DwordArithmetic.length,Nat.add_assoc] using (by assumption)
  · intro valid
    exact ⟨valid.codeFits,valid.scalarFits,valid.maskFits,valid.separate,valid.scalarOutside,valid.maskOutside,
      by simpa [offset,target,raw,DwordArithmetic.length,Nat.add_assoc] using valid.ranges 0,
      by simpa [offset,target,raw,DwordArithmetic.length,Nat.add_assoc] using valid.ranges 1,
      by simpa [offset,target,raw,DwordArithmetic.length,Nat.add_assoc] using valid.ranges 2,
      by simpa [offset,target,raw,DwordArithmetic.length,Nat.add_assoc] using valid.ranges 3,
      by simpa [offset,target,raw,DwordArithmetic.length,Nat.add_assoc] using valid.ranges 4⟩

end SmcTuring.Appendix.DwordComparison
