module
public import SmcTuring.Appendix.Listing8CopiedPointerWrites
public import SmcTuring.Appendix.Listing8OwnerSequence
public import SmcTuring.Native.StringDwordWritesBridge

public section
namespace SmcTuring.Appendix.Listing8OwnerSequenceWrites
open Native Listing8OwnerSequence Listing8Prototypes

/-- Static bounds for complete reader packets/words or the scalar target.
There is no current or future machine state in this placement predicate. -/
@[expose] def Placement (mode : Mode) (codeStart codeEnd : Nat) : Owner mode → Prop
  | .pointer source pc value => (codeStart≤source ∧ source+pointerSpan mode≤codeEnd) ∧
      (codeStart≤pc ∧ pc+pointerSpan mode≤codeEnd) ∧ (codeStart≤value.toNat ∧ value.toNat+mode.wordBytes≤codeEnd)
  | .scalar _ target _ => codeStart≤target ∧ target+4≤codeEnd

theorem advance_run (mode : Mode) (owner : Owner mode) (state : StringExecution.State mode)
    (valid : Valid mode owner) (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner))
    (current : Current mode owner state.principal.memory) :
    StringWrites.run mode ((forms mode owner).map (StringStoreWrites.liftDword mode)) state=advance mode owner state :=
  StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode (advance_trace mode owner state valid entry current))

theorem advance_owned (mode : Mode) (codeStart codeEnd : Nat) (owner : Owner mode) (placed : Placement mode codeStart codeEnd owner)
    (state : StringExecution.State mode) (valid : Valid mode owner)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner)) (current : Current mode owner state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd ((forms mode owner).map (StringStoreWrites.liftDword mode)) state := by
  cases owner with
  | pointer source pc value =>
    have mapped : (((Listing8CopiedPointer.forms mode source pc value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
        (Listing8CopiedPointer.forms mode source pc value).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    change StringWrites.OwnedRun mode codeStart codeEnd
      (((Listing8CopiedPointer.forms mode source pc value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) state
    rw [mapped]
    exact Listing8CopiedPointerWrites.owned mode codeStart codeEnd source pc value state entry valid.1 valid.2.1 placed.1 placed.2.1 placed.2.2 current.1 current.2
  | scalar pc target value =>
    have head:=StringStoreWrites.located mode codeStart codeEnd pc target value state entry valid.2.2
      (by have bound:=valid.2.1;omega) placed
    exact ⟨head,trivial⟩

/-- Every later current packet and PC follows from the preceding actual
execution and its byte frames. Ownership is concluded for the whole run. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (outside : ∀ writer∈owners,∀ reader∈owners,Outside mode writer reader)
    (placed : ∀ owner∈owners,Placement mode codeStart codeEnd owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd ((program mode owners).map (StringStoreWrites.liftDword mode)) state := by
  induction owners generalizing start state with
  | nil => trivial
  | cons owner owners ih =>
    have v:=valid owner (List.Mem.head _)
    have c:=current owner (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have first:=advance_owned mode codeStart codeEnd owner (placed owner (List.Mem.head _)) state v location c
    have next:=advance_pc mode owner state v location c
    have kept : Intact mode owners (advance mode owner state).principal.memory := by
      intro reader member
      exact retained mode owner reader state v location c (current reader (List.Mem.tail _ member))
        (outside owner (List.Mem.head _) reader (List.Mem.tail _ member))
    have rest:=ih _ chain.2 (fun reader member => valid reader (List.Mem.tail _ member))
      (fun writer wm reader rm => outside writer (List.Mem.tail _ wm) reader (List.Mem.tail _ rm))
      (fun reader member => placed reader (List.Mem.tail _ member)) _ next kept
    rw [program,List.flatMap_cons,List.map_append,StringWrites.owned_run_append,advance_run mode owner state v location c]
    exact ⟨first,rest⟩

end SmcTuring.Appendix.Listing8OwnerSequenceWrites
