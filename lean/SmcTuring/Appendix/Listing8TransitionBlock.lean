module
public import SmcTuring.Appendix.Listing8OriginalOwners

public section
namespace SmcTuring.Appendix.Listing8TransitionBlock
open Native Listing8Prototypes Listing8CopyImage
abbrev Owner:=Listing8OriginalOwners.Owner
@[expose] def owners (mode : Mode) (entry : Nat) (v : Values mode) : List (Owner mode) :=
  [.pointer entry v.next,.scalar (currentEntry mode entry) v.rule,.scalar (newEntry mode entry) v.fresh,
    .scalar (directionEntry mode entry) v.direction,.pointer (stateEntry mode entry) v.newState]
@[expose] def program (mode : Mode) (entry : Nat) (v : Values mode) := Listing8OriginalOwners.program mode (owners mode entry v)
@[expose] def finish (mode : Mode) (entry : Nat) (v : Values mode) (state : StringExecution.State mode) := Listing8OriginalOwners.finish mode (owners mode entry v) state
structure Bounds (mode : Mode) (entry : Nat) (v : Values mode) : Prop where
  capacity : entry+transitionSpan mode<2^(8*mode.wordBytes)
  nextOutside : v.next.toNat+mode.wordBytes ≤ entry ∨ entry+pointerSpan mode ≤ v.next.toNat
  stateOutside : v.newState.toNat+mode.wordBytes ≤ stateEntry mode entry ∨ stateEntry mode entry+pointerSpan mode ≤ v.newState.toNat

theorem contiguous (mode : Mode) (entry : Nat) (v : Values mode) : Listing8OriginalOwners.Contiguous mode entry (owners mode entry v) := by
  simp [owners,Listing8OriginalOwners.Contiguous,Listing8OriginalOwners.pc,Listing8OriginalOwners.span,
    currentEntry,newEntry,directionEntry,stateEntry,Nat.add_assoc]
theorem total (mode : Mode) (entry : Nat) (v : Values mode) : Listing8OriginalOwners.total mode (owners mode entry v)=transitionSpan mode := by
  simp [owners,Listing8OriginalOwners.total,Listing8OriginalOwners.span,transitionSpan];omega
theorem valid (mode : Mode) (entry : Nat) (v : Values mode) (bounds : Bounds mode entry v) :
    ∀ owner∈owners mode entry v,Listing8OriginalOwners.Valid mode owner := by
  have cap:=bounds.capacity
  intro owner member
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by dsimp [transitionSpan] at cap;omega,bounds.nextOutside⟩
  · change currentEntry mode entry+10<_;dsimp [currentEntry,transitionSpan] at *;omega
  · change newEntry mode entry+10<_;dsimp [newEntry,currentEntry,transitionSpan] at *;omega
  · change directionEntry mode entry+10<_;dsimp [directionEntry,newEntry,currentEntry,transitionSpan] at *;omega
  · refine ⟨?_,bounds.stateOutside⟩
    change stateEntry mode entry+pointerSpan mode<_
    dsimp [stateEntry,directionEntry,newEntry,currentEntry,transitionSpan] at *;omega

theorem current (mode : Mode) (entry : Nat) (v : Values mode) (memory : ByteMemory.Memory)
    (packet : ByteMemory.bytesAt memory entry (transitionSpan mode)=transitionBytes mode entry v.next v.newState v.rule v.fresh v.direction) :
    Listing8OriginalOwners.Intact mode (owners mode entry v) memory := by
  let a:=pointerBytes mode entry v.next
  let b:=DwordOwner.bytes mode (currentEntry mode entry) v.rule
  let c:=DwordOwner.bytes mode (newEntry mode entry) v.fresh
  let d:=DwordOwner.bytes mode (directionEntry mode entry) v.direction
  let e:=pointerBytes mode (stateEntry mode entry) v.newState
  have code : ByteMemory.bytesAt memory entry (a++b++c++d++e).length=a++b++c++d++e := by
    change ByteMemory.bytesAt memory entry (transitionBytes mode entry v.next v.newState v.rule v.fresh v.direction).length=_
    rw [transition_length];exact packet
  have first:=ByteWindow.packet memory entry [] a (b++c++d++e) (by simpa only [List.nil_append,List.append_assoc] using code)
  have second:=ByteWindow.packet memory entry a b (c++d++e) (by simpa only [List.append_assoc] using code)
  have third:=ByteWindow.packet memory entry (a++b) c (d++e) (by simpa only [List.append_assoc] using code)
  have fourth:=ByteWindow.packet memory entry (a++b++c) d e code
  have fifth:=ByteWindow.packet memory entry (a++b++c++d) e [] (by simpa only [List.append_nil] using code)
  intro owner member
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · simpa only [Listing8OriginalOwners.Current,List.length_nil,Nat.add_zero] using first
  · simpa only [Listing8OriginalOwners.Current,a,b,pointer_length,DwordOwner.length,currentEntry] using second
  · simpa only [Listing8OriginalOwners.Current,a,b,c,List.length_append,pointer_length,DwordOwner.length,newEntry,currentEntry,Nat.add_assoc] using third
  · simpa only [Listing8OriginalOwners.Current,a,b,c,d,List.length_append,pointer_length,DwordOwner.length,directionEntry,newEntry,currentEntry,Nat.add_assoc] using fourth
  · simpa only [Listing8OriginalOwners.Current,a,b,c,d,e,List.length_append,pointer_length,DwordOwner.length,stateEntry,directionEntry,newEntry,currentEntry,Nat.add_assoc] using fifth

theorem trace (mode : Mode) (entry : Nat) (v : Values mode) (bounds : Bounds mode entry v) (state : StringExecution.State mode)
    (location : state.principal.pc=Arithmetic.encodeNat mode entry)
    (packet : ByteMemory.bytesAt state.principal.memory entry (transitionSpan mode)=transitionBytes mode entry v.next v.newState v.rule v.fresh v.direction) :
    StringDword.Trace mode state (program mode entry v) (finish mode entry v state) :=
  Listing8OriginalOwners.trace mode (owners mode entry v) entry (contiguous mode entry v) (valid mode entry v bounds) state location (current mode entry v _ packet)
theorem result (mode : Mode) (entry : Nat) (v : Values mode) (bounds : Bounds mode entry v) (state : StringExecution.State mode)
    (location : state.principal.pc=Arithmetic.encodeNat mode entry)
    (packet : ByteMemory.bytesAt state.principal.memory entry (transitionSpan mode)=transitionBytes mode entry v.next v.newState v.rule v.fresh v.direction) :
    (finish mode entry v state).principal.pc=Arithmetic.encodeNat mode (entry+transitionSpan mode) ∧
    (finish mode entry v state).principal.memory=state.principal.memory ∧
    (finish mode entry v state).principal.stack=state.principal.stack ∧
    (finish mode entry v state).principal.carry=state.principal.carry ∧
    (finish mode entry v state).sourceIndex=state.sourceIndex ∧
    (finish mode entry v state).destinationIndex=state.destinationIndex ∧
    (finish mode entry v state).backwards=state.backwards := by
  have result:=Listing8OriginalOwners.result mode (owners mode entry v) entry (contiguous mode entry v) (valid mode entry v bounds) state location (current mode entry v _ packet)
  rw [total] at result
  exact result
theorem instruction_count (mode : Mode) (entry : Nat) (v : Values mode) : (program mode entry v).length=11 := by
  simp [program,owners,Listing8OriginalOwners.program,Listing8OriginalOwners.forms,Listing8CopiedPointer.forms]
end SmcTuring.Appendix.Listing8TransitionBlock
