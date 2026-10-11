module
public import SmcTuring.Appendix.Listing8NodeBlock

public section
namespace SmcTuring.Appendix.Listing8NodeTable
open Native Listing8Prototypes Listing8NodeBlock
@[expose] def bytes (mode : Mode) : Nat → List (Values mode) → List LittleEndian.Byte
  | _,[] => []
  | start,v::table => Listing8NodeBlock.bytes mode start v++
      bytes mode (start+nodeSpan mode) table
@[expose] def endPC (mode : Mode) (start : Nat) (table : List (Values mode)) := start+table.length*nodeSpan mode
@[expose] def entryPC (mode : Mode) (start index : Nat) := start+index*nodeSpan mode
@[expose] def owners (mode : Mode) : Nat → List (Values mode) → List (Listing8OriginalOwners.Owner mode)
  | _,[] => []
  | start,v::table => Listing8NodeBlock.owners mode start v++owners mode (start+nodeSpan mode) table
@[expose] def Valid (mode : Mode) : Nat → List (Values mode) → Prop
  | _,[] => True
  | start,v::table => Listing8NodeBlock.Bounds mode start v ∧ Valid mode (start+nodeSpan mode) table
@[expose] def Initial (mode : Mode) (start : Nat) (table : List (Values mode)) (memory : ByteMemory.Memory) :=
  ByteMemory.bytesAt memory start (bytes mode start table).length=bytes mode start table
@[expose] def image (mode : Mode) (start : Nat) (table : List (Values mode)) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes backing start (bytes mode start table)
theorem bytes_length (mode : Mode) (start : Nat) (table : List (Values mode)) :
    (bytes mode start table).length=table.length*nodeSpan mode := by
  induction table generalizing start with
  | nil => simp only [bytes,List.length_nil,Nat.zero_mul]
  | cons v table ih =>
    rw [bytes,List.length_append]
    simp only [Listing8NodeBlock.bytes,node_length]
    rw [ih,List.length_cons,Nat.add_mul]
    omega

theorem endpoint (mode : Mode) (start : Nat) (table : List (Values mode)) :
    start+(bytes mode start table).length=endPC mode start table := by rw [bytes_length];rfl

theorem initial_image (mode : Mode) (start : Nat) (table : List (Values mode)) (backing : ByteMemory.Memory) :
    Initial mode start table (image mode start table backing) := ByteMemory.bytes_at_put _ _ _

theorem head_current (mode : Mode) (start : Nat) (v : Values mode) (table : List (Values mode)) (memory : ByteMemory.Memory)
    (initial : Initial mode start (v::table) memory) :
    ByteMemory.bytesAt memory start (nodeSpan mode)=Listing8NodeBlock.bytes mode start v := by
  have packet:=ByteWindow.packet memory start [] (Listing8NodeBlock.bytes mode start v)
    (bytes mode (start+nodeSpan mode) table) (by simpa only [Initial,bytes,List.nil_append] using initial)
  simpa only [List.length_nil,Nat.add_zero,Listing8NodeBlock.bytes,node_length] using packet

theorem tail_current (mode : Mode) (start : Nat) (v : Values mode) (table : List (Values mode)) (memory : ByteMemory.Memory)
    (initial : Initial mode start (v::table) memory) : Initial mode (start+nodeSpan mode) table memory := by
  have packet:=ByteWindow.packet memory start (Listing8NodeBlock.bytes mode start v)
    (bytes mode (start+nodeSpan mode) table) [] (by simpa only [Initial,bytes,List.append_nil] using initial)
  simpa only [Initial,Listing8NodeBlock.bytes,node_length] using packet

/-- Any selected original input-node blueprint is derived by finite lookup
and slicing the complete initialized table. The index is initial data. -/
theorem selected_current (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : table[index]?=some v) (memory : ByteMemory.Memory) (initial : Initial mode start table memory) :
    ByteMemory.bytesAt memory (entryPC mode start index) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (entryPC mode start index) v := by
  induction table generalizing start index with
  | nil => simp only [List.getElem?_nil] at selected;cases selected
  | cons head table ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      subst head
      simpa only [entryPC,Nat.zero_mul,Nat.add_zero] using head_current mode start v table memory initial
    | succ index =>
      simp only [List.getElem?_cons_succ] at selected
      have next:=ih (start+nodeSpan mode) index selected (tail_current mode start head table memory initial)
      have address : entryPC mode start (index+1)=entryPC mode (start+nodeSpan mode) index := by
        simp only [entryPC,Nat.add_mul,Nat.one_mul]
        omega
      rw [address]
      exact next

theorem selected_overlay (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : table[index]?=some v) (memory : ByteMemory.Memory) (initial : Initial mode start table memory) :
    ByteMemory.putBytes memory (entryPC mode start index)
      (Listing8NodeBlock.bytes mode (entryPC mode start index) v)=memory := by
  apply ByteMemory.put_current
  rw [Listing8NodeBlock.bytes,node_length]
  exact selected_current mode start table index v selected memory initial

theorem selected_bounds (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : table[index]?=some v) :
    start≤entryPC mode start index ∧ entryPC mode start index+nodeSpan mode≤endPC mode start table := by
  have small : index<table.length := List.getElem?_eq_some_iff.mp selected |>.1
  have mult:=Nat.mul_le_mul_right (nodeSpan mode) (show index+1≤table.length by omega)
  simp only [Nat.add_mul,Nat.one_mul] at mult
  dsimp [entryPC,endPC]
  omega

end SmcTuring.Appendix.Listing8NodeTable
