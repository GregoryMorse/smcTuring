module
public import SmcTuring.Native.PayloadTemplate
public import SmcTuring.Appendix.Listing8CopiedPointerWrites
public import SmcTuring.Native.StringStoreWrites

public section
namespace SmcTuring.Appendix.Listing8PointerTemplate
open Native Listing8Prototypes Listing8CopiedPointer

@[expose] def fixed (mode : Mode) (source : Nat) :=
  Native.encode mode (.memory .exchangeAcc (ReaderImage.firstDisp mode source)) ++
    Native.encode mode (Reader.storeForm mode (ReaderImage.label mode source) (ReaderImage.secondDisp mode)) ++
    Native.encode mode .exchangeIndirect ++ wordPrefix mode ++ [0xa3]
@[expose] def Intact (mode : Mode) (source copied : Nat) (memory : ByteMemory.Memory) :=
  PayloadTemplate.Prefix memory copied (fixed mode source)

theorem fixed_length (mode : Mode) (source : Nat) :
    (fixed mode source).length=ReaderImage.labelOffset mode :=
  pointer_prefix_length mode source

theorem initial (mode : Mode) (source copied : Nat) (value : Word mode) (memory : ByteMemory.Memory)
    (packet : ByteMemory.bytesAt memory copied (pointerBytes mode source value).length=pointerBytes mode source value) :
    Intact mode source copied memory := by
  have shape : pointerBytes mode source value=fixed mode source++LittleEndian.wordEncode mode.wordBytes value :=
    pointer_shape mode source value
  have head := ByteWindow.packet memory copied [] (fixed mode source)
    (LittleEndian.wordEncode mode.wordBytes value) (by simpa only [List.nil_append,shape] using packet)
  simpa only [Intact,PayloadTemplate.Prefix,List.length_nil,Nat.add_zero] using head

/-- Arbitrary current operand bytes retain the complete printed template.
The value is reconstructed from this physical copy, never supplied by a future image. -/
theorem current (mode : Mode) (source copied : Nat) (memory : ByteMemory.Memory)
    (intact : Intact mode source copied memory) :
    let value := Protected.wordAt mode memory (pointerField mode copied)
    ByteMemory.bytesAt memory copied (pointerBytes mode source value).length=pointerBytes mode source value := by
  have ready := PayloadTemplate.current mode memory copied (fixed mode source) intact
  have extent : (fixed mode source).length+mode.wordBytes=pointerSpan mode := by
    rw [fixed_length];cases mode <;> rfl
  rw [extent] at ready
  dsimp only
  rw [pointer_length,pointer_shape]
  change ByteMemory.bytesAt memory copied (pointerSpan mode)=
    fixed mode source++LittleEndian.wordEncode mode.wordBytes (Protected.wordAt mode memory (pointerField mode copied))
  simpa only [fixed_length,pointerField] using ready

theorem operand_store (mode : Mode) (source copied : Nat) (memory : ByteMemory.Memory)
    (intact : Intact mode source copied memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (lower : pointerField mode copied≤address)
    (upper : address+bytes.length≤copied+pointerSpan mode) :
    Intact mode source copied (ByteMemory.putBytes memory address bytes) := by
  apply (PayloadTemplate.operand_store mode memory copied (fixed mode source) address bytes intact ?_ ?_).1
  · simpa only [fixed_length,pointerField] using lower
  · cases mode <;> simpa only [fixed_length,pointerField,pointerSpan,ReaderImage.totalSize,
      ReaderImage.labelOffset,Mode.wordBytes,Nat.add_assoc] using upper

theorem frame (mode : Mode) (source copied : Nat) (memory : ByteMemory.Memory)
    (intact : Intact mode source copied memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (apart : address+bytes.length≤copied ∨ copied+pointerSpan mode≤address) :
    Intact mode source copied (ByteMemory.putBytes memory address bytes) := by
  apply PayloadTemplate.frame memory copied (fixed mode source) address bytes intact
  intro index inside
  have small : index.val<ReaderImage.labelOffset mode := by simpa only [fixed_length] using index.isLt
  unfold ByteMemory.Inside at inside
  cases mode <;> simp only [pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset] at * <;>
    rcases apart with before | after <;> omega

theorem string_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringForm.Form mode)
    (packet : StringForm.fetch mode memory pc=some form) :
    StringStack.fetch mode memory pc=some (StringWrites.liftString mode form) :=
  StringStack.previous_fetch mode memory pc _
    (StringControl.previous_fetch mode memory pc _ (StringDword.string_fetch mode memory pc form packet))

/-- All four static instruction boundaries decode, including the last
MOFFS while its operand temporarily contains an arbitrary accumulator. -/
theorem decodes (mode : Mode) (source copied : Nat) (memory : ByteMemory.Memory)
    (intact : Intact mode source copied memory) :
    let value := Protected.wordAt mode memory (pointerField mode copied)
    StringStack.fetch mode memory copied=some (StringWrites.liftNative mode (first mode source copied)) ∧
    StringStack.fetch mode memory (copied+ReaderImage.firstSize mode)=
      some (StringWrites.liftNative mode (second mode source copied)) ∧
    StringStack.fetch mode memory (copied+ReaderImage.firstSize mode+ReaderImage.secondSize mode)=
      some (StringWrites.liftNative mode .exchangeIndirect) ∧
    StringStack.fetch mode memory (copied+ReaderImage.prefixSize mode)=
      some (StringWrites.liftNative mode (.moffs value)) := by
  let value := Protected.wordAt mode memory (pointerField mode copied)
  let a := Native.encode mode (first mode source copied)
  let b := Native.encode mode (second mode source copied)
  let c := Native.encode mode .exchangeIndirect
  let d := Native.encode mode (.moffs value)
  have shape : pointerBytes mode source value=a++b++c++d := by
    simpa only [forms,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
      StringForm.encode,List.append_assoc] using (encoding mode source copied value).symm
  have code : ByteMemory.bytesAt memory copied (a++b++c++d).length=a++b++c++d := by
    rw [←shape];exact current mode source copied memory intact
  have one := ByteWindow.packet memory copied [] a (b++c++d)
    (by simpa only [List.nil_append,List.append_assoc] using code)
  have two := ByteWindow.packet memory copied a b (c++d)
    (by simpa only [List.append_assoc] using code)
  have three := ByteWindow.packet memory copied (a++b) c d code
  have four := ByteWindow.packet memory copied (a++b++c) d []
    (by simpa only [List.append_nil] using code)
  have lenA : a.length=ReaderImage.firstSize mode := by cases mode <;> rfl
  have lenAB : (a++b).length=ReaderImage.firstSize mode+ReaderImage.secondSize mode := by cases mode <;> rfl
  have lenABC : (a++b++c).length=ReaderImage.prefixSize mode := by cases mode <;> rfl
  refine ⟨string_fetch mode memory copied _ (StringForm.fetch_current_encoding mode memory copied _ (by trivial) ?_),
    string_fetch mode memory _ _ (StringForm.fetch_current_encoding mode memory _ _ (by trivial) ?_),
    string_fetch mode memory _ _ (StringForm.fetch_current_encoding mode memory _ _ (by trivial) ?_),
    string_fetch mode memory _ _ (StringForm.fetch_current_encoding mode memory _ _ (by trivial) ?_)⟩
  · simpa only [List.length_nil,Nat.add_zero,StringForm.encode,a] using one
  · simpa only [lenA,StringForm.encode,b] using two
  · simpa only [lenAB,Nat.add_assoc,StringForm.encode,c] using three
  · simpa only [lenABC,StringForm.encode,d,value] using four

end SmcTuring.Appendix.Listing8PointerTemplate
