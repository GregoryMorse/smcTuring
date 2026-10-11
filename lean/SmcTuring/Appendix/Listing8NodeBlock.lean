module
public import SmcTuring.Appendix.Listing8OriginalOwners

public section
namespace SmcTuring.Appendix.Listing8NodeBlock
open Native Listing8Prototypes
structure Values (mode : Mode) where
  symbol : BitVec 32
  back : Word mode
  forward : Word mode
@[expose] def bytes (mode : Mode) (entry : Nat) (v : Values mode) := nodeBytes mode entry v.symbol v.back v.forward
@[expose] def owners (mode : Mode) (entry : Nat) (v : Values mode) : List (Listing8OriginalOwners.Owner mode) :=
  [.scalar entry v.symbol,.pointer (backEntry mode entry) v.back,.pointer (forwardEntry mode entry) v.forward]
@[expose] def program (mode : Mode) (entry : Nat) (v : Values mode) := Listing8OriginalOwners.program mode (owners mode entry v)
@[expose] def finish (mode : Mode) (entry : Nat) (v : Values mode) (state : StringExecution.State mode) := Listing8OriginalOwners.finish mode (owners mode entry v) state
structure Bounds (mode : Mode) (entry : Nat) (v : Values mode) : Prop where
  capacity : entry+nodeSpan mode<2^(8*mode.wordBytes)
  backOutside : v.back.toNat+mode.wordBytes≤backEntry mode entry ∨ backEntry mode entry+pointerSpan mode≤v.back.toNat
  forwardOutside : v.forward.toNat+mode.wordBytes≤forwardEntry mode entry ∨ forwardEntry mode entry+pointerSpan mode≤v.forward.toNat

theorem contiguous (mode : Mode) (entry : Nat) (v : Values mode) : Listing8OriginalOwners.Contiguous mode entry (owners mode entry v) := by
  simp [owners,Listing8OriginalOwners.Contiguous,Listing8OriginalOwners.pc,Listing8OriginalOwners.span,backEntry,forwardEntry]
theorem total (mode : Mode) (entry : Nat) (v : Values mode) : Listing8OriginalOwners.total mode (owners mode entry v)=nodeSpan mode := by
  simp [owners,Listing8OriginalOwners.total,Listing8OriginalOwners.span,nodeSpan];omega
theorem valid (mode : Mode) (entry : Nat) (v : Values mode) (bounds : Bounds mode entry v) :
    ∀ owner∈owners mode entry v,Listing8OriginalOwners.Valid mode owner := by
  have cap:=bounds.capacity
  intro owner member
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · change entry+10<_
    dsimp [nodeSpan] at cap;omega
  · refine ⟨?_,bounds.backOutside⟩
    dsimp [backEntry,nodeSpan] at cap ⊢;omega
  · refine ⟨?_,bounds.forwardOutside⟩
    dsimp [forwardEntry,backEntry,nodeSpan] at cap ⊢;omega
theorem current (mode : Mode) (entry : Nat) (v : Values mode) (memory : ByteMemory.Memory)
    (packet : ByteMemory.bytesAt memory entry (nodeSpan mode)=bytes mode entry v) :
    Listing8OriginalOwners.Intact mode (owners mode entry v) memory := by
  have full : ByteMemory.bytesAt memory entry (nodeBytes mode entry v.symbol v.back v.forward).length=
      nodeBytes mode entry v.symbol v.back v.forward := by rw [node_length];exact packet
  intro owner member
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact node_symbol_current mode entry v.symbol v.back v.forward memory full
  · exact node_back_current mode entry v.symbol v.back v.forward memory full
  · exact node_forward_current mode entry v.symbol v.back v.forward memory full
theorem trace (mode : Mode) (entry : Nat) (v : Values mode) (bounds : Bounds mode entry v)
    (state : StringExecution.State mode) (location : state.principal.pc=Arithmetic.encodeNat mode entry)
    (packet : ByteMemory.bytesAt state.principal.memory entry (nodeSpan mode)=bytes mode entry v) :
    StringDword.Trace mode state (program mode entry v) (finish mode entry v state) :=
  Listing8OriginalOwners.trace mode (owners mode entry v) entry (contiguous mode entry v) (valid mode entry v bounds)
    state location (current mode entry v _ packet)
theorem result (mode : Mode) (entry : Nat) (v : Values mode) (bounds : Bounds mode entry v)
    (state : StringExecution.State mode) (location : state.principal.pc=Arithmetic.encodeNat mode entry)
    (packet : ByteMemory.bytesAt state.principal.memory entry (nodeSpan mode)=bytes mode entry v) :
    (finish mode entry v state).principal.pc=Arithmetic.encodeNat mode (entry+nodeSpan mode) ∧
    (finish mode entry v state).principal.memory=state.principal.memory ∧
    (finish mode entry v state).principal.stack=state.principal.stack ∧
    (finish mode entry v state).principal.carry=state.principal.carry ∧
    (finish mode entry v state).sourceIndex=state.sourceIndex ∧
    (finish mode entry v state).destinationIndex=state.destinationIndex ∧
    (finish mode entry v state).backwards=state.backwards := by
  have actual:=Listing8OriginalOwners.result mode (owners mode entry v) entry (contiguous mode entry v) (valid mode entry v bounds)
    state location (current mode entry v _ packet)
  rw [total] at actual
  exact actual
theorem instruction_count (mode : Mode) (entry : Nat) (v : Values mode) : (program mode entry v).length=9 := by
  cases mode <;> rfl
end SmcTuring.Appendix.Listing8NodeBlock
