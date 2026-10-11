module
public import SmcTuring.Native.ReaderImage
public import SmcTuring.Native.DwordOwner
public import SmcTuring.Native.ByteWindow
public import SmcTuring.Native.MixedMemory
public import SmcTuring.Native.StringMacroTrace
public import SmcTuring.Native.DwordMixedImage

public section
namespace SmcTuring.Appendix.Listing8Prototypes
open Native
abbrev Dword := BitVec 32

/-- The entry of the four-instruction M01 DEFADDR is distinct from its
label, which denotes the final MOFFS operand field. -/
@[expose] def pointerBytes (mode : Mode) (entry : Nat) (value : Word mode) :=
  ((ReaderImage.packets mode entry value).map (ControlImage.Packet.bytes mode)).flatten
@[expose] def pointerField (mode : Mode) (entry : Nat) := entry+ReaderImage.labelOffset mode
@[expose] def pointerSpan (mode : Mode) := ReaderImage.totalSize mode

theorem pointer_length (mode : Mode) (entry : Nat) (value : Word mode) :
    (pointerBytes mode entry value).length = pointerSpan mode := by
  simpa only [pointerBytes,pointerSpan,ControlPacking.size,List.length_flatten,List.map_map,Function.comp_def]
    using ReaderImage.packet_size mode entry value

theorem pointer_shape (mode : Mode) (entry : Nat) (value : Word mode) :
    pointerBytes mode entry value =
      (Native.encode mode (.memory .exchangeAcc (ReaderImage.firstDisp mode entry)) ++
        Native.encode mode (Reader.storeForm mode (ReaderImage.label mode entry) (ReaderImage.secondDisp mode)) ++
        Native.encode mode .exchangeIndirect ++ wordPrefix mode ++ [0xa3]) ++
      LittleEndian.wordEncode mode.wordBytes value := by
  simp [pointerBytes,ReaderImage.packets,ControlImage.Packet.bytes,Native.encode,List.append_assoc]

theorem pointer_prefix_length (mode : Mode) (entry : Nat) :
    (Native.encode mode (.memory .exchangeAcc (ReaderImage.firstDisp mode entry)) ++
      Native.encode mode (Reader.storeForm mode (ReaderImage.label mode entry) (ReaderImage.secondDisp mode)) ++
      Native.encode mode .exchangeIndirect ++ wordPrefix mode ++ [0xa3]).length = ReaderImage.labelOffset mode := by
  cases mode <;> rfl

theorem pointer_value (mode : Mode) (entry : Nat) (value : Word mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory entry (pointerBytes mode entry value).length = pointerBytes mode entry value) :
    MixedMemory.getWord mode memory (pointerField mode entry) = value := by
  have packet := ByteWindow.packet memory entry
    (Native.encode mode (.memory .exchangeAcc (ReaderImage.firstDisp mode entry)) ++
      Native.encode mode (Reader.storeForm mode (ReaderImage.label mode entry) (ReaderImage.secondDisp mode)) ++
      Native.encode mode .exchangeIndirect ++ wordPrefix mode ++ [0xa3])
    (LittleEndian.wordEncode mode.wordBytes value) []
    (by simpa [pointer_shape,List.append_assoc] using current)
  rw [pointer_prefix_length,LittleEndian.word_encode_length] at packet
  have decoded : ByteMemory.readWord mode memory (pointerField mode entry) = some value := by
    change LittleEndian.wordDecode mode.wordBytes (ByteMemory.bytesAt memory (pointerField mode entry) mode.wordBytes) = some value
    rw [pointerField,packet,LittleEndian.word_decode_encode]
  rw [MixedMemory.read_total] at decoded
  exact Option.some.inj decoded

theorem pointer_label_is_not_entry (mode : Mode) (entry : Nat) : entry < pointerField mode entry := by
  cases mode <;> simp [pointerField,ReaderImage.labelOffset]

/-- The generalized node described immediately before Listing 7 has one
symbol owner followed by the two complete back/forward DEFADDR owners. -/
@[expose] def backEntry (_mode : Mode) (entry : Nat) := entry+10
@[expose] def forwardEntry (mode : Mode) (entry : Nat) := backEntry mode entry+pointerSpan mode
@[expose] def nodeSpan (mode : Mode) := 10+2*pointerSpan mode
@[expose] def nodeBytes (mode : Mode) (entry : Nat) (symbol : Dword) (back forward : Word mode) :=
  DwordOwner.bytes mode entry symbol ++ pointerBytes mode (backEntry mode entry) back ++
    pointerBytes mode (forwardEntry mode entry) forward

theorem node_length (mode : Mode) (entry : Nat) (symbol : Dword) (back forward : Word mode) :
    (nodeBytes mode entry symbol back forward).length = nodeSpan mode := by
  simp only [nodeBytes,List.length_append,DwordOwner.length,pointer_length,nodeSpan]
  omega

theorem node_sizes : nodeSpan .x86 = 46 ∧ nodeSpan .x64 = 64 := ⟨rfl,rfl⟩

theorem node_symbol_current (mode : Mode) (entry : Nat) (symbol : Dword) (back forward : Word mode)
    (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory entry (nodeBytes mode entry symbol back forward).length = nodeBytes mode entry symbol back forward) :
    ByteMemory.bytesAt memory entry 10 = DwordOwner.bytes mode entry symbol := by
  have packet := ByteWindow.packet memory entry [] (DwordOwner.bytes mode entry symbol)
    (pointerBytes mode (backEntry mode entry) back ++ pointerBytes mode (forwardEntry mode entry) forward)
    (by simpa [nodeBytes,List.append_assoc] using current)
  simpa only [List.length_nil,Nat.add_zero,DwordOwner.length] using packet

theorem node_back_current (mode : Mode) (entry : Nat) (symbol : Dword) (back forward : Word mode)
    (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory entry (nodeBytes mode entry symbol back forward).length = nodeBytes mode entry symbol back forward) :
    ByteMemory.bytesAt memory (backEntry mode entry) (pointerBytes mode (backEntry mode entry) back).length =
      pointerBytes mode (backEntry mode entry) back := by
  have packet := ByteWindow.packet memory entry (DwordOwner.bytes mode entry symbol)
    (pointerBytes mode (backEntry mode entry) back) (pointerBytes mode (forwardEntry mode entry) forward)
    (by simpa [nodeBytes,List.append_assoc] using current)
  simpa only [DwordOwner.length,backEntry] using packet

theorem node_forward_current (mode : Mode) (entry : Nat) (symbol : Dword) (back forward : Word mode)
    (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory entry (nodeBytes mode entry symbol back forward).length = nodeBytes mode entry symbol back forward) :
    ByteMemory.bytesAt memory (forwardEntry mode entry) (pointerBytes mode (forwardEntry mode entry) forward).length =
      pointerBytes mode (forwardEntry mode entry) forward := by
  have packet := ByteWindow.packet memory entry
    (DwordOwner.bytes mode entry symbol ++ pointerBytes mode (backEntry mode entry) back)
    (pointerBytes mode (forwardEntry mode entry) forward) []
    (by simpa [nodeBytes,List.append_assoc] using current)
  simpa only [List.length_append,DwordOwner.length,pointer_length,forwardEntry,backEntry,Nat.add_assoc] using packet

theorem node_values (mode : Mode) (entry : Nat) (symbol : Dword) (back forward : Word mode)
    (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory entry (nodeBytes mode entry symbol back forward).length = nodeBytes mode entry symbol back forward) :
    DwordCode.get memory (entry+6) = symbol ∧
    MixedMemory.getWord mode memory (pointerField mode (backEntry mode entry)) = back ∧
    MixedMemory.getWord mode memory (pointerField mode (forwardEntry mode entry)) = forward := by
  have operand := DwordOwner.current_immediate mode entry symbol memory
    (node_symbol_current mode entry symbol back forward memory current)
  have decoded : ByteMemory.readWord .x86 memory (entry+6) = some symbol := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt memory (entry+6) 4) = some symbol
    rw [operand,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact ⟨Option.some.inj decoded,
    pointer_value mode _ back memory (node_back_current mode entry symbol back forward memory current),
    pointer_value mode _ forward memory (node_forward_current mode entry symbol back forward memory current)⟩

/-- Listing 7: next pointer, current symbol, new symbol, direction, new-state
pointer. All entry PCs and operand labels follow from the selected encoder. -/
@[expose] def currentEntry (mode : Mode) (entry : Nat) := entry+pointerSpan mode
@[expose] def newEntry (mode : Mode) (entry : Nat) := currentEntry mode entry+10
@[expose] def directionEntry (mode : Mode) (entry : Nat) := newEntry mode entry+10
@[expose] def stateEntry (mode : Mode) (entry : Nat) := directionEntry mode entry+10
@[expose] def transitionSpan (mode : Mode) := 2*pointerSpan mode+30
@[expose] def transitionBytes (mode : Mode) (entry : Nat) (next state : Word mode)
    (current fresh direction : Dword) :=
  pointerBytes mode entry next ++ DwordOwner.bytes mode (currentEntry mode entry) current ++
    DwordOwner.bytes mode (newEntry mode entry) fresh ++ DwordOwner.bytes mode (directionEntry mode entry) direction ++
    pointerBytes mode (stateEntry mode entry) state

theorem transition_length (mode : Mode) (entry : Nat) (next state : Word mode) (current fresh direction : Dword) :
    (transitionBytes mode entry next state current fresh direction).length = transitionSpan mode := by
  simp only [transitionBytes,List.length_append,DwordOwner.length,pointer_length,transitionSpan]
  omega

theorem transition_sizes : transitionSpan .x86 = 66 ∧ transitionSpan .x64 = 84 := ⟨rfl,rfl⟩

theorem transition_values (mode : Mode) (entry : Nat) (next state : Word mode) (current fresh direction : Dword)
    (memory : ByteMemory.Memory)
    (intact : ByteMemory.bytesAt memory entry (transitionBytes mode entry next state current fresh direction).length =
      transitionBytes mode entry next state current fresh direction) :
    MixedMemory.getWord mode memory (pointerField mode entry) = next ∧
    DwordCode.get memory (currentEntry mode entry+6) = current ∧
    DwordCode.get memory (newEntry mode entry+6) = fresh ∧
    DwordCode.get memory (directionEntry mode entry+6) = direction ∧
    MixedMemory.getWord mode memory (pointerField mode (stateEntry mode entry)) = state := by
  have a := ByteWindow.packet memory entry [] (pointerBytes mode entry next)
    (DwordOwner.bytes mode (currentEntry mode entry) current ++ DwordOwner.bytes mode (newEntry mode entry) fresh ++
      DwordOwner.bytes mode (directionEntry mode entry) direction ++ pointerBytes mode (stateEntry mode entry) state)
    (by simpa [transitionBytes,List.append_assoc] using intact)
  have b := ByteWindow.packet memory entry (pointerBytes mode entry next)
    (DwordOwner.bytes mode (currentEntry mode entry) current)
    (DwordOwner.bytes mode (newEntry mode entry) fresh ++ DwordOwner.bytes mode (directionEntry mode entry) direction ++
      pointerBytes mode (stateEntry mode entry) state)
    (by simpa [transitionBytes,List.append_assoc] using intact)
  have c := ByteWindow.packet memory entry (pointerBytes mode entry next ++ DwordOwner.bytes mode (currentEntry mode entry) current)
    (DwordOwner.bytes mode (newEntry mode entry) fresh)
    (DwordOwner.bytes mode (directionEntry mode entry) direction ++ pointerBytes mode (stateEntry mode entry) state)
    (by simpa [transitionBytes,List.append_assoc] using intact)
  have d := ByteWindow.packet memory entry
    (pointerBytes mode entry next ++ DwordOwner.bytes mode (currentEntry mode entry) current ++ DwordOwner.bytes mode (newEntry mode entry) fresh)
    (DwordOwner.bytes mode (directionEntry mode entry) direction) (pointerBytes mode (stateEntry mode entry) state)
    (by simpa [transitionBytes,List.append_assoc] using intact)
  have e := ByteWindow.packet memory entry
    (pointerBytes mode entry next ++ DwordOwner.bytes mode (currentEntry mode entry) current ++
      DwordOwner.bytes mode (newEntry mode entry) fresh ++ DwordOwner.bytes mode (directionEntry mode entry) direction)
    (pointerBytes mode (stateEntry mode entry) state) []
    (by simpa [transitionBytes,List.append_assoc] using intact)
  have getOwner (pc : Nat) (value : Dword) (packet : ByteMemory.bytesAt memory pc 10 = DwordOwner.bytes mode pc value) :
      DwordCode.get memory (pc+6) = value := by
    have operand := DwordOwner.current_immediate mode pc value memory packet
    have decoded : ByteMemory.readWord .x86 memory (pc+6) = some value := by
      change LittleEndian.wordDecode 4 (ByteMemory.bytesAt memory (pc+6) 4) = some value
      rw [operand,LittleEndian.word_decode_encode]
    rw [DwordCode.read_total] at decoded
    exact Option.some.inj decoded
  refine ⟨pointer_value mode entry next memory (by simpa using a),?_,?_,?_,?_⟩
  · exact getOwner _ _ (by simpa only [pointer_length,DwordOwner.length,currentEntry] using b)
  · exact getOwner _ _ (by simpa only [List.length_append,pointer_length,DwordOwner.length,newEntry,currentEntry,Nat.add_assoc] using c)
  · exact getOwner _ _ (by simpa only [List.length_append,pointer_length,DwordOwner.length,directionEntry,newEntry,currentEntry,Nat.add_assoc] using d)
  · exact pointer_value mode _ state memory (by
      simpa only [List.length_append,pointer_length,DwordOwner.length,stateEntry,directionEntry,newEntry,currentEntry,Nat.add_assoc] using e)

end SmcTuring.Appendix.Listing8Prototypes
