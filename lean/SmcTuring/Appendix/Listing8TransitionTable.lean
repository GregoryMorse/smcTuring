module
public import SmcTuring.Appendix.Listing8TransitionBlock

public section
namespace SmcTuring.Appendix.Listing8TransitionTable
open Native Listing8Prototypes Listing8CopyImage
@[expose] def bytes (mode : Mode) : Nat → List (Values mode) → List LittleEndian.Byte
  | _,[] => []
  | start,v::table => transitionBytes mode start v.next v.newState v.rule v.fresh v.direction++
      bytes mode (start+transitionSpan mode) table
@[expose] def endPC (mode : Mode) (start : Nat) (table : List (Values mode)) := start+table.length*transitionSpan mode
@[expose] def entryPC (mode : Mode) (start index : Nat) := start+index*transitionSpan mode
@[expose] def owners (mode : Mode) : Nat → List (Values mode) → List (Listing8OriginalOwners.Owner mode)
  | _,[] => []
  | start,v::table => Listing8TransitionBlock.owners mode start v++owners mode (start+transitionSpan mode) table
@[expose] def Valid (mode : Mode) : Nat → List (Values mode) → Prop
  | _,[] => True
  | start,v::table => Listing8TransitionBlock.Bounds mode start v ∧ Valid mode (start+transitionSpan mode) table
@[expose] def Initial (mode : Mode) (start : Nat) (table : List (Values mode)) (memory : ByteMemory.Memory) :=
  ByteMemory.bytesAt memory start (bytes mode start table).length=bytes mode start table
@[expose] def image (mode : Mode) (start : Nat) (table : List (Values mode)) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes backing start (bytes mode start table)
/- Only the five declared transition fields determine table membership;
the current tape symbol and neighbors are independent body inputs. -/
@[expose] def Selected (mode : Mode) (table : List (Values mode)) (index : Nat) (v : Values mode) : Prop :=
  ∃ declared,table[index]?=some declared ∧ declared.next=v.next ∧ declared.newState=v.newState ∧
    declared.rule=v.rule ∧ declared.fresh=v.fresh ∧ declared.direction=v.direction

theorem bytes_length (mode : Mode) (start : Nat) (table : List (Values mode)) :
    (bytes mode start table).length=table.length*transitionSpan mode := by
  induction table generalizing start with
  | nil => simp only [bytes,List.length_nil,Nat.zero_mul]
  | cons v table ih =>
    rw [bytes,List.length_append,transition_length,ih,List.length_cons,Nat.add_mul]
    omega

theorem endpoint (mode : Mode) (start : Nat) (table : List (Values mode)) :
    start+(bytes mode start table).length=endPC mode start table := by rw [bytes_length];rfl

theorem initial_image (mode : Mode) (start : Nat) (table : List (Values mode)) (backing : ByteMemory.Memory) :
    Initial mode start table (image mode start table backing) := ByteMemory.bytes_at_put _ _ _

theorem head_current (mode : Mode) (start : Nat) (v : Values mode) (table : List (Values mode)) (memory : ByteMemory.Memory)
    (initial : Initial mode start (v::table) memory) :
    ByteMemory.bytesAt memory start (transitionSpan mode)=transitionBytes mode start v.next v.newState v.rule v.fresh v.direction := by
  have packet:=ByteWindow.packet memory start [] (transitionBytes mode start v.next v.newState v.rule v.fresh v.direction)
    (bytes mode (start+transitionSpan mode) table) (by simpa only [Initial,bytes,List.nil_append] using initial)
  simpa only [List.length_nil,Nat.add_zero,transition_length] using packet

theorem tail_current (mode : Mode) (start : Nat) (v : Values mode) (table : List (Values mode)) (memory : ByteMemory.Memory)
    (initial : Initial mode start (v::table) memory) : Initial mode (start+transitionSpan mode) table memory := by
  have packet:=ByteWindow.packet memory start (transitionBytes mode start v.next v.newState v.rule v.fresh v.direction)
    (bytes mode (start+transitionSpan mode) table) [] (by simpa only [Initial,bytes,List.append_nil] using initial)
  simpa only [Initial,transition_length] using packet

/-- Any selected original transition blueprint is derived by finite lookup
and slicing the complete initialized table. The index is initial data. -/
theorem selected_current (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : table[index]?=some v) (memory : ByteMemory.Memory) (initial : Initial mode start table memory) :
    ByteMemory.bytesAt memory (entryPC mode start index) (transitionSpan mode)=
      transitionBytes mode (entryPC mode start index) v.next v.newState v.rule v.fresh v.direction := by
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
      have next:=ih (start+transitionSpan mode) index selected (tail_current mode start head table memory initial)
      have address : entryPC mode start (index+1)=entryPC mode (start+transitionSpan mode) index := by
        simp only [entryPC,Nat.add_mul,Nat.one_mul]
        omega
      rw [address]
      exact next

theorem selected_overlay (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : table[index]?=some v) (memory : ByteMemory.Memory) (initial : Initial mode start table memory) :
    ByteMemory.putBytes memory (entryPC mode start index)
      (transitionBytes mode (entryPC mode start index) v.next v.newState v.rule v.fresh v.direction)=memory := by
  apply ByteMemory.put_current
  rw [transition_length]
  exact selected_current mode start table index v selected memory initial

theorem selected_bounds (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : table[index]?=some v) :
    start≤entryPC mode start index ∧ entryPC mode start index+transitionSpan mode≤endPC mode start table := by
  have small : index<table.length := List.getElem?_eq_some_iff.mp selected |>.1
  have mult:=Nat.mul_le_mul_right (transitionSpan mode) (show index+1≤table.length by omega)
  simp only [Nat.add_mul,Nat.one_mul] at mult
  dsimp [entryPC,endPC]
  omega

theorem from_lookup (mode : Mode) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : table[index]?=some v) : Selected mode table index v := ⟨v,selected,rfl,rfl,rfl,rfl,rfl⟩

theorem fields_current (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : Selected mode table index v) (memory : ByteMemory.Memory) (initial : Initial mode start table memory) :
    ByteMemory.bytesAt memory (entryPC mode start index) (transitionSpan mode)=
      transitionBytes mode (entryPC mode start index) v.next v.newState v.rule v.fresh v.direction := by
  rcases selected with ⟨declared,lookup,next,state,rule,fresh,direction⟩
  have packet:=selected_current mode start table index declared lookup memory initial
  rw [next,state,rule,fresh,direction] at packet
  exact packet

theorem fields_overlay (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : Selected mode table index v) (memory : ByteMemory.Memory) (initial : Initial mode start table memory) :
    ByteMemory.putBytes memory (entryPC mode start index)
      (transitionBytes mode (entryPC mode start index) v.next v.newState v.rule v.fresh v.direction)=memory := by
  apply ByteMemory.put_current
  rw [transition_length]
  exact fields_current mode start table index v selected memory initial

theorem fields_bounds (mode : Mode) (start : Nat) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : Selected mode table index v) :
    start≤entryPC mode start index ∧ entryPC mode start index+transitionSpan mode≤endPC mode start table := by
  rcases selected with ⟨declared,lookup,_⟩
  exact selected_bounds mode start table index declared lookup
end SmcTuring.Appendix.Listing8TransitionTable
