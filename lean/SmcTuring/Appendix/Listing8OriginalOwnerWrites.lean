module
public import SmcTuring.Appendix.Listing8OwnerSequenceWrites
public import SmcTuring.Appendix.Listing8OriginalOwners

public section
namespace SmcTuring.Appendix.Listing8OriginalOwnerWrites
open Native Listing8OriginalOwners Listing8Prototypes

@[expose] def Placement (mode : Mode) (codeStart codeEnd : Nat) : Owner mode → Prop
  | .pointer pc value => (codeStart≤pc ∧ pc+pointerSpan mode≤codeEnd) ∧
      (codeStart≤value.toNat ∧ value.toNat+mode.wordBytes≤codeEnd)
  | .scalar pc _ => codeStart≤pc+6 ∧ pc+10≤codeEnd

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
  | pointer pc value =>
    have mapped : (((Listing8CopiedPointer.forms mode pc pc value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
        (Listing8CopiedPointer.forms mode pc pc value).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    change StringWrites.OwnedRun mode codeStart codeEnd
      (((Listing8CopiedPointer.forms mode pc pc value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) state
    rw [mapped]
    exact Listing8CopiedPointerWrites.owned mode codeStart codeEnd pc pc value state entry valid.1 valid.1
      placed.1 placed.1 placed.2 current current
  | scalar pc value =>
    have inside : codeStart≤pc+6 ∧ pc+10≤codeEnd := placed
    have store:=StringStoreWrites.located mode codeStart codeEnd pc (pc+6) value state entry
      (fun _ => DwordOwner.reach pc) (by change pc+10<_ at valid;omega) (by change codeStart≤pc+6 ∧ pc+6+4≤codeEnd;omega)
    exact ⟨store,trivial⟩

/-- Original declaration packets derive indirect targets; every owner restores
whole memory before the next declaration, with no future image premise. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
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
    have effect:=advance_effect mode owner state v location c
    have next : (advance mode owner state).principal.pc=Arithmetic.encodeNat mode (pc mode owner+span mode owner) := by rw [effect]
    have kept : Intact mode owners (advance mode owner state).principal.memory := by
      rw [effect];intro reader member;exact current reader (List.Mem.tail _ member)
    have rest:=ih _ chain.2 (fun reader member => valid reader (List.Mem.tail _ member))
      (fun reader member => placed reader (List.Mem.tail _ member)) _ next kept
    rw [program,List.flatMap_cons,List.map_append,StringWrites.owned_run_append,advance_run mode owner state v location c]
    exact ⟨first,rest⟩

end SmcTuring.Appendix.Listing8OriginalOwnerWrites
