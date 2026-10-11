module
public import SmcTuring.Native.AccumulatorEffects

public section
namespace SmcTuring.Native.AccumulatorImage
open Execution AccumulatorLayout AccumulatorEffects ControlImage

theorem save_address (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) :
    Writes.address mode (saveForm mode layout) state = Arithmetic.encodeNat mode layout.save :=
  Reader.store_write_address mode state _ _ (save_hits mode layout valid state entry)

theorem first_address (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    Writes.address mode (first mode layout) state = Arithmetic.encodeNat mode layout.pointer :=
  first_hits mode layout valid state entry

theorem second_address (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    Writes.address mode (second mode layout) state = Arithmetic.encodeNat mode layout.pointer :=
  Reader.store_write_address mode state _ _ (second_hits mode layout valid state entry)

theorem third_address (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    Writes.address mode (third mode layout) state = Arithmetic.encodeNat mode layout.save :=
  third_hits mode layout valid state entry

theorem supported_run (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) (owns : Word mode → Prop)
    (save : owns (Arithmetic.encodeNat mode layout.save)) (pointer : owns (Arithmetic.encodeNat mode layout.pointer)) :
    Writes.OwnedRun mode owns (program mode layout) state := by
  change owns (Writes.address mode (first mode layout) state) ∧
    owns (Writes.address mode (second mode layout) (swapped mode layout state)) ∧
    owns (Writes.address mode (third mode layout) (restored mode layout state)) ∧ True
  rw [first_address mode layout valid state entry,
    second_address mode layout valid _ (swapped_pc mode layout valid state entry),
    third_address mode layout valid _ (restored_pc mode layout valid state entry)]
  exact ⟨pointer,pointer,save,trivial⟩

theorem saved_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) (whole : List (Entry mode))
    (separate : Separated mode whole) (intact : Intact mode whole state.memory)
    (save : Owned mode whole (Arithmetic.encodeNat mode layout.save)) :
    Intact mode whole (saved mode layout state).memory := by
  apply execute_intact mode whole state (saveForm mode layout) separate intact
  rwa [save_address mode layout valid state entry]

theorem swapped_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) (whole : List (Entry mode))
    (separate : Separated mode whole) (intact : Intact mode whole state.memory)
    (pointer : Owned mode whole (Arithmetic.encodeNat mode layout.pointer)) :
    Intact mode whole (swapped mode layout state).memory := by
  apply execute_intact mode whole state (first mode layout) separate intact
  rwa [first_address mode layout valid state entry]

theorem restored_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) (whole : List (Entry mode))
    (separate : Separated mode whole) (intact : Intact mode whole state.memory)
    (pointer : Owned mode whole (Arithmetic.encodeNat mode layout.pointer)) :
    Intact mode whole (restored mode layout state).memory := by
  apply execute_intact mode whole (swapped mode layout state) (second mode layout) separate
    (swapped_intact mode layout valid state entry whole separate intact pointer)
  rwa [second_address mode layout valid _ (swapped_pc mode layout valid state entry)]

theorem finish_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) (whole : List (Entry mode))
    (separate : Separated mode whole) (intact : Intact mode whole state.memory)
    (save : Owned mode whole (Arithmetic.encodeNat mode layout.save))
    (pointer : Owned mode whole (Arithmetic.encodeNat mode layout.pointer)) :
    Intact mode whole (finish mode layout state).memory := by
  apply execute_intact mode whole (restored mode layout state) (third mode layout) separate
    (restored_intact mode layout valid state entry whole separate intact pointer)
  rwa [third_address mode layout valid _ (restored_pc mode layout valid state entry)]

theorem fetched (mode : Mode) (whole : List (Entry mode)) (state : State mode) (pc : Nat) (form : Form mode)
    (member : (⟨pc,.fixed form⟩ : Entry mode) ∈ whole) (intact : Intact mode whole state.memory)
    (location : state.pc = Arithmetic.encodeNat mode pc) (fits : pc < 2 ^ (8 * mode.wordBytes)) :
    Fetch.fetch mode state.memory state.pc.toNat = some form := by
  rw [location,Arithmetic.encode_nat_toNat mode pc fits]
  exact fetch_current mode ⟨pc,.fixed form⟩ state.memory (intact _ member)

theorem save_trace (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) (whole : List (Entry mode))
    (included : ∀ helper ∈ entries mode layout, helper ∈ whole) (intact : Intact mode whole state.memory) :
    Fetch.Trace mode state [saveForm mode layout] (saved mode layout state) := by
  have member := included _ (List.Mem.head _)
  have fits : layout.prologue < 2 ^ (8 * mode.wordBytes) := by
    have bound := valid.prologueFits; unfold savedPC at bound; omega
  exact .step (fetched mode whole state _ _ member intact entry fits) (.nil _)

theorem trace (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) (whole : List (Entry mode))
    (included : ∀ helper ∈ entries mode layout, helper ∈ whole)
    (separate : Separated mode whole) (intact : Intact mode whole state.memory)
    (_save : Owned mode whole (Arithmetic.encodeNat mode layout.save))
    (pointer : Owned mode whole (Arithmetic.encodeNat mode layout.pointer)) :
    Fetch.Trace mode state (program mode layout) (finish mode layout state) := by
  have bound := valid.epilogueFits
  have epiFits : layout.epilogue < 2 ^ (8 * mode.wordBytes) := by
    unfold endPC thirdPC secondPC at bound; omega
  have secondFits : secondPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    unfold endPC thirdPC at bound; omega
  have thirdFits : thirdPC mode layout < 2 ^ (8 * mode.wordBytes) := by unfold endPC at bound; omega
  have firstMember := included _ (List.Mem.tail _ (List.Mem.head _))
  have secondMember := included _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have thirdMember := included _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have firstFetch := fetched mode whole state _ _ firstMember intact entry epiFits
  have secondFetch := fetched mode whole (swapped mode layout state) _ _ secondMember
    (swapped_intact mode layout valid state entry whole separate intact pointer)
    (swapped_pc mode layout valid state entry) secondFits
  have thirdFetch := fetched mode whole (restored mode layout state) _ _ thirdMember
    (restored_intact mode layout valid state entry whole separate intact pointer)
    (restored_pc mode layout valid state entry) thirdFits
  exact .step firstFetch (.step secondFetch (.step thirdFetch (.nil _)))

/-- Metadata ownership and its initial value are both derived from the
actual emitted operand bytes. Storage owners need not be executed. -/
theorem owner_value (mode : Mode) (whole : List (Entry mode)) (backing : ByteMemory.Memory)
    (separate : Separated mode whole) (owner : Nat) (value : Word mode)
    (member : (⟨owner,.owned value⟩ : Entry mode) ∈ whole)
    (fits : owner + moffsOperandOffset mode < 2 ^ (8 * mode.wordBytes)) :
    load mode (image mode whole backing) (Arithmetic.encodeNat mode (owner + moffsOperandOffset mode)) = value := by
  let memory := image mode whole backing
  have packet := image_packet mode whole backing separate ⟨owner,.owned value⟩ member
  have headerCurrent : Protected.PrefixAt mode memory owner :=
    initialized_intact mode whole backing separate _ member
  have full : ByteMemory.bytesAt memory owner (moffsOperandOffset mode + mode.wordBytes) =
      Protected.opcode mode ++ LittleEndian.wordEncode mode.wordBytes value := by
    simpa only [Entry.bytes,Packet.bytes,encode,moffsOperandOffset,Protected.opcode,
      List.length_append,List.length_cons,List.length_nil,LittleEndian.word_encode_length]
      using packet
  rw [Protected.bytes_at_append, headerCurrent] at full
  have payload := List.append_cancel_left full
  have loaded := read_word_total mode memory (Arithmetic.encodeNat mode (owner + moffsOperandOffset mode))
  rw [Arithmetic.encode_nat_toNat mode _ fits,ByteMemory.readWord,payload,
    LittleEndian.word_decode_encode] at loaded
  exact Option.some.inj loaded.symm

theorem owner_owned (mode : Mode) (whole : List (Entry mode)) (owner : Nat) (value : Word mode)
    (member : (⟨owner,.owned value⟩ : Entry mode) ∈ whole)
    (fits : owner + moffsOperandOffset mode < 2 ^ (8 * mode.wordBytes)) :
    Owned mode whole (Arithmetic.encodeNat mode (owner + moffsOperandOffset mode)) := by
  refine ⟨⟨owner,.owned value⟩,member,⟨value,rfl⟩,?_⟩
  exact Arithmetic.encode_nat_toNat mode _ fits

theorem load_agreement (mode : Mode) (first second : ByteMemory.Memory) (field : Nat)
    (fits : field < 2 ^ (8 * mode.wordBytes))
    (same : ∀ index : Fin mode.wordBytes, first (field + index.val) = second (field + index.val)) :
    load mode first (Arithmetic.encodeNat mode field) = load mode second (Arithmetic.encodeNat mode field) := by
  unfold load
  rw [Arithmetic.encode_nat_toNat mode field fits]
  congr 2
  unfold ByteMemory.bytesAt
  exact congrArg List.ofFn (funext same)

end SmcTuring.Native.AccumulatorImage
