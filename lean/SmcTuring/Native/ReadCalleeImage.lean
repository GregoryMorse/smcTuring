module
public import SmcTuring.Native.CallsImage

public section

namespace SmcTuring.Native.ReadCalleeImage

open Execution ControlImage

@[expose] def callStart (mode : Mode) (start : Nat) : Nat := start + ReaderImage.totalSize mode
@[expose] def totalSize : Mode -> Nat | .x86 => 36 | .x64 => 47

@[expose] def params (mode : Mode) (start top slot : Nat) : ReadCallee.Params mode :=
  { label := ReaderImage.label mode start, top := Arithmetic.encodeNat mode top, slot := Arithmetic.encodeNat mode slot,
    readFirst := ReaderImage.firstDisp mode start, readSecond := ReaderImage.secondDisp mode,
    resetFirst := CallsImage.firstDisp mode (callStart mode start) top,
    resetSecond := CallsImage.secondDisp mode (callStart mode start) top,
    returnDisp := Relocation.instructionDisp mode .callIndirect (callStart mode start + CallsImage.resetSize mode) slot }

@[expose] def packets (mode : Mode) (start top slot : Nat) (initial : Word mode) : List (Packet mode) :=
  ReaderImage.packets mode start initial ++ CallsImage.packets mode (callStart mode start) top (.indirect slot)

abbrev Ranges (mode : Mode) (start top slot : Nat) :=
  CallsImage.Ranges mode (callStart mode start) top (.indirect slot)

theorem packet_size (mode : Mode) (start top slot : Nat) (initial : Word mode) :
    ControlPacking.size mode (packets mode start top slot initial) = totalSize mode := by
  rw [packets, Fragment.size_append, ReaderImage.packet_size, CallsImage.packet_size]
  cases mode <;> rfl

theorem reader_within (mode : Mode) (start top slot : Nat) (initial : Word mode) :
    Fragment.Within mode (ControlPacking.place mode start (ReaderImage.packets mode start initial))
      (ControlPacking.place mode start (packets mode start top slot initial)) :=
  Fragment.prefix_within mode start _ _

theorem call_within (mode : Mode) (start top slot : Nat) (initial : Word mode) :
    Fragment.Within mode (ControlPacking.place mode (callStart mode start) (CallsImage.packets mode (callStart mode start) top (.indirect slot)))
      (ControlPacking.place mode start (packets mode start top slot initial)) := by
  have view := Fragment.suffix_within mode start (ReaderImage.packets mode start initial)
    (CallsImage.packets mode (callStart mode start) top (.indirect slot))
  rw [ReaderImage.packet_size] at view
  exact view

theorem read_pc (mode : Mode) (start top slot : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (ReadCallee.readEnd mode (params mode start top slot) state).pc = Arithmetic.encodeNat mode (callStart mode start) :=
  ReaderImage.finish_pc mode start state location

theorem read_memory (mode : Mode) (start top slot : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (ReadCallee.readEnd mode (params mode start top slot) state).memory = state.memory :=
  Reader.finish_memory mode state _ _ _ (ReaderImage.first_hits mode start state location)
    (ReaderImage.second_hits mode start state location)

/-- Every resolved-address premise of the seven-instruction local contract is
derived from the computed displacements and initialized StackTop word. -/
theorem ready (mode : Mode) (start top slot : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes) :
    ReadCallee.Ready mode (params mode start top slot) state := by
  constructor
  · exact ReaderImage.first_hits mode start state location
  · exact ReaderImage.second_hits mode start state location
  · apply CallsImage.stack_ready mode (callStart mode start) top slot (.indirect slot) _
      (read_pc mode start top slot state location) ranges
    rw [read_memory mode start top slot state location]
    exact value
  · exact CallsImage.indirect_hits mode (callStart mode start) top slot _
      (read_pc mode start top slot state location) ranges

theorem return_next (mode : Mode) (start top slot : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    ReadCallee.returnNext mode (params mode start top slot) state = Arithmetic.encodeNat mode (start + totalSize mode) := by
  have next := CallsImage.return_next mode (callStart mode start) top (.indirect slot)
    (ReadCallee.readEnd mode (params mode start top slot) state) (read_pc mode start top slot state location)
  have length : callStart mode start + CallsImage.totalSize mode (.indirect slot) = start + totalSize mode := by
    cases mode <;> simp [callStart, ReaderImage.totalSize, CallsImage.totalSize, CallsImage.resetSize, totalSize, Nat.add_assoc]
  rw [length] at next
  exact next

theorem reader_fits (mode : Mode) (start : Nat)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes)) :
    start + ReaderImage.totalSize mode < 2 ^ (8 * mode.wordBytes) := by
  cases mode <;> simp [totalSize, ReaderImage.totalSize, Mode.wordBytes] at * <;> omega

theorem call_fits (mode : Mode) (start slot : Nat)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes)) :
    callStart mode start + CallsImage.totalSize mode (.indirect slot) < 2 ^ (8 * mode.wordBytes) := by
  cases mode <;> simpa [callStart, ReaderImage.totalSize, CallsImage.totalSize, CallsImage.resetSize, totalSize, Nat.add_assoc] using fits

/-- Constructed seven-instruction callee within a complete byte image. All
automatic fetches and resolved-address equations are discharged here. Actual
code-field ownership and finite placement are the remaining image inputs. -/
theorem trace (mode : Mode) (start top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : origin + SpacedPacking.size mode whole <= gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top slot initial))
      (SpacedPacking.place mode origin whole))
    (intact : SpacedCombinedImage.Intact mode whole origin gridBase state.memory)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase (load mode state.memory (ReaderImage.label mode start)))
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top)) :
    Fetch.Trace mode state (ReadCallee.program mode (params mode start top slot) state)
      (ReadCallee.finish mode (params mode start top slot) state) := by
  have leading := ReaderView.trace mode start origin gridBase initial whole state location
    (reader_fits mode start fits) enough gap
    (Fragment.within_trans mode _ _ _ (reader_within mode start top slot initial) within) intact pointerOwned
  have readIntact : SpacedCombinedImage.Intact mode whole origin gridBase
      (ReadCallee.readEnd mode (params mode start top slot) state).memory := by
    rw [read_memory mode start top slot state location]; exact intact
  have trailing := CallsImage.trace mode (callStart mode start) top origin gridBase (.indirect slot) whole
    (ReadCallee.readEnd mode (params mode start top slot) state) (read_pc mode start top slot state location) ranges
    (call_fits mode start slot fits) enough gap
    (Fragment.within_trans mode _ _ _ (call_within mode start top slot initial) within) readIntact topOwned
  exact Fetch.trace_append mode leading trailing

theorem owned_run (mode : Mode) (start top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top slot initial))
      (SpacedPacking.place mode origin whole))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase (load mode state.memory (ReaderImage.label mode start)))
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top))
    (slotOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode slot)) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode whole origin gridBase)
      (ReadCallee.program mode (params mode start top slot) state) state := by
  apply ReadCallee.owned_run mode (params mode start top slot) state (ready mode start top slot state location ranges value)
    (SpacedCombinedImage.Owned mode whole origin gridBase)
  · exact Or.inl (ReaderView.label_owned mode start origin initial whole (reader_fits mode start fits)
      (Fragment.within_trans mode _ _ _ (reader_within mode start top slot initial) within))
  · exact pointerOwned
  · exact topOwned
  · exact slotOwned

theorem finish_intact (mode : Mode) (start top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : origin + SpacedPacking.size mode whole <= gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top slot initial))
      (SpacedPacking.place mode origin whole))
    (intact : SpacedCombinedImage.Intact mode whole origin gridBase state.memory)
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase (load mode state.memory (ReaderImage.label mode start)))
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top))
    (slotOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode slot)) :
    SpacedCombinedImage.Intact mode whole origin gridBase (ReadCallee.finish mode (params mode start top slot) state).memory :=
  SpacedCombinedImage.trace_intact mode whole origin gridBase state _ _ enough gap intact
    (owned_run mode start top slot origin gridBase initial whole state location ranges fits within value pointerOwned topOwned slotOwned)
    (trace mode start top slot origin gridBase initial whole state location ranges fits enough gap within intact pointerOwned topOwned)

theorem memory_effect (mode : Mode) (start top slot : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (slotFits : slot < 2 ^ (8 * mode.wordBytes))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes) :
    (ReadCallee.finish mode (params mode start top slot) state).memory =
      ByteMemory.putWord mode state.memory slot (Arithmetic.encodeNat mode (start + totalSize mode)) := by
  rw [ReadCallee.memory_effect mode _ state (ready mode start top slot state location ranges value),
    return_next mode start top slot state location]
  simp only [params, Arithmetic.encode_nat_toNat mode slot slotFits]

theorem boundary_effect (mode : Mode) (start top slot : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (slotFits : slot < 2 ^ (8 * mode.wordBytes))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes) :
    And ((ReadCallee.finish mode (params mode start top slot) state).pc = load mode state.memory (Arithmetic.encodeNat mode slot))
      (And ((ReadCallee.finish mode (params mode start top slot) state).memory =
        ByteMemory.putWord mode state.memory slot (Arithmetic.encodeNat mode (start + totalSize mode)))
        (And ((ReadCallee.finish mode (params mode start top slot) state).accumulator =
          load mode state.memory (load mode state.memory (ReaderImage.label mode start)))
          (And ((ReadCallee.finish mode (params mode start top slot) state).stack = Arithmetic.encodeNat mode slot)
            ((ReadCallee.finish mode (params mode start top slot) state).carry = state.carry)))) := by
  have resolved := ready mode start top slot state location ranges value
  exact ⟨ReadCallee.target_pc mode _ state resolved, memory_effect mode start top slot state location ranges slotFits value,
    ReadCallee.accumulator mode _ state resolved, ReadCallee.stack mode _ state resolved, ReadCallee.carry mode _ state⟩

theorem top_reusable (mode : Mode) (start top slot origin gridBase : Nat) (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (gap : origin + SpacedPacking.size mode whole <= gridBase - moffsOperandOffset mode)
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top))
    (slotOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode slot))
    (different : Not (Arithmetic.encodeNat mode top = Arithmetic.encodeNat mode slot)) :
    load mode (ReadCallee.finish mode (params mode start top slot) state).memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes :=
  ReadCallee.top_word mode _ state (ready mode start top slot state location ranges value)
    (Fragment.owned_fields_separate mode whole origin gridBase _ _ gap topOwned slotOwned different)

theorem initial_pointer (mode : Mode) (start top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top slot initial))
      (SpacedPacking.place mode origin whole)) :
    load mode (SpacedCombinedImage.image mode whole origin gridBase values) (ReaderImage.label mode start) = initial := by
  have member : List.Mem (ReaderImage.lastEntry mode start initial)
      (ControlPacking.place mode start (ReaderImage.packets mode start initial)) := by
    rw [ReaderImage.placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  exact Fragment.initialized_owned_word mode whole origin gridBase values (ReaderImage.lastEntry mode start initial)
    (within _ (reader_within mode start top slot initial _ member)) initial (ReaderImage.label mode start) rfl
    (ReaderImage.label_location mode start initial (reader_fits mode start fits))

theorem initialized_ready (mode : Mode) (start top slot origin gridBase : Nat) (whole : List (SpacedPacking.Piece mode))
    (values : Nat -> Word mode) (state : State mode) (topEntry : Entry mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (memory : state.memory = SpacedCombinedImage.image mode whole origin gridBase values)
    (ranges : Ranges mode start top slot)
    (member : List.Mem topEntry (SpacedPacking.place mode origin whole))
    (kind : topEntry.packet = .owned (Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes))
    (topLocation : (Arithmetic.encodeNat mode top).toNat = topEntry.pc + moffsOperandOffset mode) :
    ReadCallee.Ready mode (params mode start top slot) state := by
  apply ready mode start top slot state location ranges
  rw [memory]
  exact Fragment.initialized_owned_word mode whole origin gridBase values topEntry member _ _ kind topLocation

theorem initialized_trace (mode : Mode) (start top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode) (state : State mode) (topEntry : Entry mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (memory : state.memory = SpacedCombinedImage.image mode whole origin gridBase values)
    (ranges : Ranges mode start top slot) (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : origin + SpacedPacking.size mode whole <= gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top slot initial))
      (SpacedPacking.place mode origin whole))
    (member : List.Mem topEntry (SpacedPacking.place mode origin whole))
    (kind : topEntry.packet = .owned (Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes))
    (topLocation : (Arithmetic.encodeNat mode top).toNat = topEntry.pc + moffsOperandOffset mode)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase initial) :
    Fetch.Trace mode state (ReadCallee.program mode (params mode start top slot) state)
      (ReadCallee.finish mode (params mode start top slot) state) := by
  apply trace mode start top slot origin gridBase initial whole state location ranges fits enough gap within
  · rw [memory]; exact SpacedCombinedImage.initially_intact mode whole origin gridBase values enough gap
  · rw [memory, initial_pointer mode start top slot origin gridBase initial whole values fits within]; exact pointerOwned
  · exact Or.inl ⟨topEntry, member, ⟨_, kind⟩, topLocation⟩

theorem initialized_owned_run (mode : Mode) (start top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode) (state : State mode) (topEntry : Entry mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (memory : state.memory = SpacedCombinedImage.image mode whole origin gridBase values)
    (ranges : Ranges mode start top slot) (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top slot initial))
      (SpacedPacking.place mode origin whole))
    (member : List.Mem topEntry (SpacedPacking.place mode origin whole))
    (kind : topEntry.packet = .owned (Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes))
    (topLocation : (Arithmetic.encodeNat mode top).toNat = topEntry.pc + moffsOperandOffset mode)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase initial)
    (slotOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode slot)) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode whole origin gridBase)
      (ReadCallee.program mode (params mode start top slot) state) state := by
  apply owned_run mode start top slot origin gridBase initial whole state location ranges fits within
  · rw [memory]
    exact Fragment.initialized_owned_word mode whole origin gridBase values topEntry member _ _ kind topLocation
  · rw [memory, initial_pointer mode start top slot origin gridBase initial whole values fits within]; exact pointerOwned
  · exact Or.inl ⟨topEntry, member, ⟨_, kind⟩, topLocation⟩
  · exact slotOwned

end SmcTuring.Native.ReadCalleeImage
