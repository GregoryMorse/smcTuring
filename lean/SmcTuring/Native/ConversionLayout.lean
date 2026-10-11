module
public import SmcTuring.Native.ControlPacking
public import SmcTuring.Native.Reader
public import SmcTuring.Native.Relocation

public section
namespace SmcTuring.Native.ConversionLayout
open Execution ControlImage

structure Layout where
  start : Nat
  source : Nat
  destination : Nat

@[expose] def exchangeSize (mode : Mode) : Nat := instructionLength mode (.memory .exchangeAcc 0)
@[expose] def storeSize (mode : Mode) : Nat := match mode with | .x86 => 5 | .x64 => 7
@[expose] def span (mode : Mode) : Nat := exchangeSize mode + storeSize mode + exchangeSize mode
@[expose] def secondPC (mode : Mode) (layout : Layout) : Nat := layout.start + exchangeSize mode
@[expose] def thirdPC (mode : Mode) (layout : Layout) : Nat := secondPC mode layout + storeSize mode
@[expose] def endPC (mode : Mode) (layout : Layout) : Nat := thirdPC mode layout + exchangeSize mode
@[expose] def firstDisp (mode : Mode) (layout : Layout) : BitVec 32 := Relocation.instructionDisp mode .exchangeAcc layout.start layout.source
@[expose] def secondDisp (mode : Mode) (layout : Layout) : BitVec 32 := Relocation.instructionDisp mode .storeAcc (secondPC mode layout) layout.destination
@[expose] def thirdDisp (mode : Mode) (layout : Layout) : BitVec 32 := Relocation.instructionDisp mode .exchangeAcc (thirdPC mode layout) layout.source
@[expose] def first (mode : Mode) (layout : Layout) : Form mode := .memory .exchangeAcc (firstDisp mode layout)
@[expose] def second (mode : Mode) (layout : Layout) : Form mode := Reader.storeForm mode (Arithmetic.encodeNat mode layout.destination) (secondDisp mode layout)
@[expose] def third (mode : Mode) (layout : Layout) : Form mode := .memory .exchangeAcc (thirdDisp mode layout)
@[expose] def program (mode : Mode) (layout : Layout) : List (Form mode) := [first mode layout, second mode layout, third mode layout]
@[expose] def packets (mode : Mode) (layout : Layout) : List (Packet mode) := (program mode layout).map Packet.fixed
@[expose] def entries (mode : Mode) (layout : Layout) : List (Entry mode) :=
  [⟨layout.start, .fixed (first mode layout)⟩, ⟨secondPC mode layout, .fixed (second mode layout)⟩, ⟨thirdPC mode layout, .fixed (third mode layout)⟩]

/-- Only initial static geometry/resources. The source/destination can be
ordinary data or code operands. Complete words are disjoint and outside this
three-instruction control fragment; signed RIP relocation limits are explicit. -/
structure Admissible (mode : Mode) (layout : Layout) : Prop where
  codeFits : endPC mode layout < 2 ^ (8 * mode.wordBytes)
  sourceFits : layout.source + mode.wordBytes ≤ 2 ^ (8 * mode.wordBytes)
  destinationFits : layout.destination + mode.wordBytes ≤ 2 ^ (8 * mode.wordBytes)
  separate : layout.source + mode.wordBytes ≤ layout.destination ∨ layout.destination + mode.wordBytes ≤ layout.source
  sourceOutside : layout.source + mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ layout.source
  destinationOutside : layout.destination + mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ layout.destination
  firstRange : mode = .x64 -> Relocation.SignedDelta (secondPC mode layout) layout.source
  secondRange : mode = .x64 -> Relocation.SignedDelta (thirdPC mode layout) layout.destination
  thirdRange : mode = .x64 -> Relocation.SignedDelta (endPC mode layout) layout.source

theorem lengths (mode : Mode) (layout : Layout) :
    instructionLength mode (first mode layout) = exchangeSize mode ∧
    instructionLength mode (second mode layout) = storeSize mode ∧
    instructionLength mode (third mode layout) = exchangeSize mode := by cases mode <;> exact ⟨rfl,rfl,rfl⟩

theorem span_size (mode : Mode) (layout : Layout) : ControlPacking.size mode (packets mode layout) = span mode := by cases mode <;> rfl

theorem placed_entries (mode : Mode) (layout : Layout) : ControlPacking.place mode layout.start (packets mode layout) = entries mode layout := by cases mode <;> rfl

theorem endpoint (mode : Mode) (layout : Layout) : endPC mode layout = layout.start + span mode := by
  unfold endPC thirdPC secondPC span
  omega

theorem separated (mode : Mode) (layout : Layout) : ControlImage.Separated mode (entries mode layout) := by
  rw [←placed_entries]
  exact ControlPacking.placed_separated mode _ _

theorem source_toNat (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    (Arithmetic.encodeNat mode layout.source).toNat = layout.source := by
  apply Arithmetic.encode_nat_toNat
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  have fits := valid.sourceFits
  omega

theorem destination_toNat (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    (Arithmetic.encodeNat mode layout.destination).toNat = layout.destination := by
  apply Arithmetic.encode_nat_toNat
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  have fits := valid.destinationFits
  omega

theorem outside (mode : Mode) (layout : Layout) (field : Nat)
    (fits : field < 2 ^ (8 * mode.wordBytes))
    (disjoint : field + mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ field) :
    ControlImage.External mode (entries mode layout) (Arithmetic.encodeNat mode field) := by
  intro entry member index
  rw [←placed_entries] at member
  have lower := ControlPacking.placed_lower mode _ _ entry member
  have upper := ControlPacking.placed_upper mode _ _ entry member
  rw [span_size, ←endpoint] at upper
  have small := index.isLt
  rw [Arithmetic.encode_nat_toNat mode field fits]
  unfold ByteMemory.Inside
  rcases disjoint with before | after <;> omega

theorem first_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    memoryAddress mode (nextPC mode (first mode layout) native) (firstDisp mode layout) = Arithmetic.encodeNat mode layout.source :=
  Relocation.instruction_memory_hits mode .exchangeAcc layout.start layout.source native entry valid.firstRange

theorem second_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    Reader.storeAddress mode native (Arithmetic.encodeNat mode layout.destination) (secondDisp mode layout) = Arithmetic.encodeNat mode layout.destination := by
  cases mode with
  | x86 => rfl
  | x64 => exact Relocation.instruction_memory_hits .x64 .storeAcc (secondPC .x64 layout) layout.destination native entry valid.secondRange

theorem third_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    memoryAddress mode (nextPC mode (third mode layout) native) (thirdDisp mode layout) = Arithmetic.encodeNat mode layout.source :=
  Relocation.instruction_memory_hits mode .exchangeAcc (thirdPC mode layout) layout.source native entry valid.thirdRange

theorem first_next (mode : Mode) (layout : Layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    nextPC mode (first mode layout) native = Arithmetic.encodeNat mode (secondPC mode layout) := by
  rw [Relocation.next_pc mode native _ _ entry, (lengths mode layout).1]
  rfl

theorem second_next (mode : Mode) (layout : Layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    nextPC mode (second mode layout) native = Arithmetic.encodeNat mode (thirdPC mode layout) := by
  rw [Relocation.next_pc mode native _ _ entry, (lengths mode layout).2.1]
  rfl

theorem third_next (mode : Mode) (layout : Layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    nextPC mode (third mode layout) native = Arithmetic.encodeNat mode (endPC mode layout) := by
  rw [Relocation.next_pc mode native _ _ entry, (lengths mode layout).2.2]
  rfl

end SmcTuring.Native.ConversionLayout
