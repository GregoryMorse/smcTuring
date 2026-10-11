module
public import SmcTuring.Native.DwordCode
public import SmcTuring.Native.ConversionLayout

public section
namespace SmcTuring.Native.DwordLayout
open DwordCode
abbrev Layout := ConversionLayout.Layout
@[expose] def storeSize (mode : Mode) : Nat := match mode with | .x86 => 5 | .x64 => 6
@[expose] def secondPC (_mode : Mode) (layout : Layout) : Nat := layout.start + 6
@[expose] def thirdPC (mode : Mode) (layout : Layout) : Nat := secondPC mode layout + storeSize mode
@[expose] def endPC (mode : Mode) (layout : Layout) : Nat := thirdPC mode layout + 6
@[expose] def span (mode : Mode) : Nat := 12 + storeSize mode
@[expose] def firstDisp (mode : Mode) (layout : Layout) : Dword :=
  Relocation.memoryDisp mode (secondPC mode layout) layout.source
@[expose] def secondDisp (mode : Mode) (layout : Layout) : Dword :=
  Relocation.memoryDisp mode (thirdPC mode layout) layout.destination
@[expose] def thirdDisp (mode : Mode) (layout : Layout) : Dword :=
  Relocation.memoryDisp mode (endPC mode layout) layout.source
@[expose] def first (mode : Mode) (layout : Layout) : DwordCode.Form mode := .exchange (firstDisp mode layout)
@[expose] def second (mode : Mode) (layout : Layout) : DwordCode.Form mode :=
  match mode with
  | .x86 => .moffs (Arithmetic.encodeNat .x86 layout.destination)
  | .x64 => .store (secondDisp .x64 layout)
@[expose] def third (mode : Mode) (layout : Layout) : DwordCode.Form mode := .exchange (thirdDisp mode layout)
@[expose] def program (mode : Mode) (layout : Layout) : List (DwordCode.Form mode) :=
  [first mode layout,second mode layout,third mode layout]

/-- Static capacities and complete four-byte separation. The long-mode
relocations use the actual six-byte DWORD instruction ends, without REX.W. -/
structure Admissible (mode : Mode) (layout : Layout) : Prop where
  codeFits : endPC mode layout < 2^(8*mode.wordBytes)
  sourceFits : layout.source+4 ≤ 2^(8*mode.wordBytes)
  destinationFits : layout.destination+4 ≤ 2^(8*mode.wordBytes)
  separate : layout.source+4 ≤ layout.destination ∨ layout.destination+4 ≤ layout.source
  sourceOutside : layout.source+4 ≤ layout.start ∨ endPC mode layout ≤ layout.source
  destinationOutside : layout.destination+4 ≤ layout.start ∨ endPC mode layout ≤ layout.destination
  firstRange : mode = .x64 → Relocation.SignedDelta (secondPC mode layout) layout.source
  secondRange : mode = .x64 → Relocation.SignedDelta (thirdPC mode layout) layout.destination
  thirdRange : mode = .x64 → Relocation.SignedDelta (endPC mode layout) layout.source

theorem lengths (mode : Mode) (layout : Layout) :
    length mode (first mode layout) = 6 ∧ length mode (second mode layout) = storeSize mode ∧
      length mode (third mode layout) = 6 := by cases mode <;> exact ⟨rfl,rfl,rfl⟩

theorem endpoint (mode : Mode) (layout : Layout) : endPC mode layout = layout.start + span mode := by
  unfold endPC thirdPC secondPC span
  omega

theorem span_sizes : span .x86 = 17 ∧ span .x64 = 18 := ⟨rfl,rfl⟩

theorem source_toNat (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    (Arithmetic.encodeNat mode layout.source).toNat = layout.source := by
  apply Arithmetic.encode_nat_toNat
  have bound := valid.sourceFits
  omega

theorem destination_toNat (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    (Arithmetic.encodeNat mode layout.destination).toNat = layout.destination := by
  apply Arithmetic.encode_nat_toNat
  have bound := valid.destinationFits
  omega

theorem next_nat (mode : Mode) (form : DwordCode.Form mode) (state : Execution.State mode) (pc : Nat)
    (location : state.pc = Arithmetic.encodeNat mode pc) :
    next mode form state = Arithmetic.encodeNat mode (pc + length mode form) := by
  rw [next,location]
  exact BitVec.ofNat_add_ofNat pc (length mode form)

theorem first_next (mode : Mode) (layout : Layout) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode layout.start) :
    next mode (first mode layout) state = Arithmetic.encodeNat mode (secondPC mode layout) := by
  rw [next_nat mode _ state _ location,(lengths mode layout).1]
  rfl

theorem second_next (mode : Mode) (layout : Layout) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    next mode (second mode layout) state = Arithmetic.encodeNat mode (thirdPC mode layout) := by
  rw [next_nat mode _ state _ location,(lengths mode layout).2.1]
  rfl

theorem third_next (mode : Mode) (layout : Layout) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    next mode (third mode layout) state = Arithmetic.encodeNat mode (endPC mode layout) := by
  rw [next_nat mode _ state _ location,(lengths mode layout).2.2]
  rfl

theorem first_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (location : state.pc = Arithmetic.encodeNat mode layout.start) :
    address mode (first mode layout) state = Arithmetic.encodeNat mode layout.source := by
  change Execution.memoryAddress mode (next mode (first mode layout) state) (firstDisp mode layout) = _
  rw [first_next mode layout state location]
  exact Relocation.memory_hits mode _ _ valid.firstRange

theorem second_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (location : state.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    address mode (second mode layout) state = Arithmetic.encodeNat mode layout.destination := by
  cases mode with
  | x86 => rfl
  | x64 =>
    change Execution.memoryAddress .x64 (next .x64 (second .x64 layout) state) (secondDisp .x64 layout) = _
    rw [second_next .x64 layout state location]
    exact Relocation.memory_hits .x64 _ _ valid.secondRange

theorem third_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (location : state.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    address mode (third mode layout) state = Arithmetic.encodeNat mode layout.source := by
  change Execution.memoryAddress mode (next mode (third mode layout) state) (thirdDisp mode layout) = _
  rw [third_next mode layout state location]
  exact Relocation.memory_hits mode _ _ valid.thirdRange

theorem source_outside (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (index : Fin 4) :
    ¬ByteMemory.Inside layout.destination 4 (layout.source+index.val) := by
  have bound := index.isLt
  have apart := valid.separate
  unfold ByteMemory.Inside
  omega

theorem destination_outside (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (index : Fin 4) :
    ¬ByteMemory.Inside layout.source 4 (layout.destination+index.val) := by
  have bound := index.isLt
  have apart := valid.separate
  unfold ByteMemory.Inside
  omega

@[expose] def reachable (mode : Mode) (next target : Nat) : Bool :=
  match mode with
  | .x86 => true
  | .x64 => decide (-(2^31 : Int) ≤ (target : Int)-(next : Int)) &&
      decide ((target : Int)-(next : Int) < (2^31 : Int))

theorem reachable_iff (mode : Mode) (next target : Nat) :
    reachable mode next target = true ↔ (mode = .x64 → Relocation.SignedDelta next target) := by
  cases mode <;> simp [reachable,Relocation.SignedDelta,Relocation.delta]

@[expose] def checks (mode : Mode) (layout : Layout) : List Bool :=
  [decide (endPC mode layout < 2^(8*mode.wordBytes)),
   decide (layout.source+4 ≤ 2^(8*mode.wordBytes)),
   decide (layout.destination+4 ≤ 2^(8*mode.wordBytes)),
   decide (layout.source+4 ≤ layout.destination ∨ layout.destination+4 ≤ layout.source),
   decide (layout.source+4 ≤ layout.start ∨ endPC mode layout ≤ layout.source),
   decide (layout.destination+4 ≤ layout.start ∨ endPC mode layout ≤ layout.destination),
   reachable mode (secondPC mode layout) layout.source,
   reachable mode (thirdPC mode layout) layout.destination,
   reachable mode (endPC mode layout) layout.source]

theorem checks_valid (mode : Mode) (layout : Layout) :
    (checks mode layout).all id = true ↔ Admissible mode layout := by
  constructor
  · intro h
    simp only [checks,List.all_cons,List.all_nil,id_eq,Bool.and_eq_true, and_true,
      decide_eq_true_eq,reachable_iff] at h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2⟩
  · intro valid
    simp only [checks,List.all_cons,List.all_nil,id_eq,Bool.and_eq_true,and_true,
      decide_eq_true_eq,reachable_iff]
    exact ⟨valid.codeFits,valid.sourceFits,valid.destinationFits,valid.separate,valid.sourceOutside,
      valid.destinationOutside,valid.firstRange,valid.secondRange,valid.thirdRange⟩

end SmcTuring.Native.DwordLayout
