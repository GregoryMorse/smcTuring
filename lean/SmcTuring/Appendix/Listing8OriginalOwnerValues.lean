module
public import SmcTuring.Appendix.Listing8TransitionBlock

public section
namespace SmcTuring.Appendix.Listing8OriginalOwnerValues
open Native Listing8Prototypes Listing8OriginalOwners
@[expose] def finalAccumulator (mode : Mode) : List (Owner mode) → ByteMemory.Memory → Word mode → Word mode
  | [],_,acc => acc
  | .pointer _ value::owners,memory,_ => finalAccumulator mode owners memory (Execution.load mode memory value)
  | .scalar _ _::owners,memory,acc => finalAccumulator mode owners memory acc
theorem accumulator_result (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    (finish mode owners state).principal.accumulator=finalAccumulator mode owners state.principal.memory state.principal.accumulator := by
  induction owners generalizing start state with
  | nil => rfl
  | cons owner owners ih =>
    have v:=valid owner (List.mem_cons_self ..)
    have c:=current owner (List.mem_cons_self ..)
    have loc : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have effect:=advance_effect mode owner state v loc c
    have next : (advance mode owner state).principal.pc=Arithmetic.encodeNat mode (pc mode owner+span mode owner) := by rw [effect]
    have remaining : Intact mode owners (advance mode owner state).principal.memory := by
      rw [effect];intro reader member;exact current reader (List.mem_cons_of_mem _ member)
    have rest:=ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next remaining
    change (finish mode owners (advance mode owner state)).principal.accumulator=_
    rw [rest,effect]
    cases owner <;> rfl

theorem transition_accumulator (mode : Mode) (entry : Nat) (v : Listing8CopyImage.Values mode)
    (bounds : Listing8TransitionBlock.Bounds mode entry v) (state : StringExecution.State mode)
    (location : state.principal.pc=Arithmetic.encodeNat mode entry)
    (packet : ByteMemory.bytesAt state.principal.memory entry (transitionSpan mode)=transitionBytes mode entry v.next v.newState v.rule v.fresh v.direction) :
    (Listing8TransitionBlock.finish mode entry v state).principal.accumulator=Execution.load mode state.principal.memory v.newState := by
  rw [Listing8TransitionBlock.finish,accumulator_result mode (Listing8TransitionBlock.owners mode entry v) entry
    (Listing8TransitionBlock.contiguous mode entry v) (Listing8TransitionBlock.valid mode entry v bounds) state location
    (Listing8TransitionBlock.current mode entry v _ packet)]
  rfl
end SmcTuring.Appendix.Listing8OriginalOwnerValues
