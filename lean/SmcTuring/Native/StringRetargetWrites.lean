module
public import SmcTuring.Native.StringStoreWrites
public import SmcTuring.Native.StringRetarget

public section
namespace SmcTuring.Native.StringRetargetWrites
open DwordRetargetSequence

/-- Actual reached PCs resolve every retarget store into its complete
four-byte owner field. Future PCs and ownership follow by execution. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (sites : List Site) (start : Nat)
    (chain : Contiguous start sites) (valid : ∀ site∈sites,Valid mode site)
    (fields : ∀ site∈sites,codeStart≤site.owner+2 ∧ site.owner+6≤codeEnd)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringRetarget.program mode sites).map (StringStoreWrites.liftDword mode)) state := by
  induction sites generalizing start state with
  | nil => trivial
  | cons site sites ih =>
    have ready:=valid site (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have head:=StringStoreWrites.located mode codeStart codeEnd site.pc (site.owner+2)
      (DwordRetarget.printed mode site.pc site.owner site.destination) state location ready.2.2 (by have fits:=ready.2.1;omega)
      (by have bound:=fields site (List.Mem.head _);exact ⟨bound.1,by omega⟩)
    have next:=StringStoreWrites.next_pc mode (Relocation.memoryDisp mode (site.pc+10) (site.owner+2))
      (DwordRetarget.printed mode site.pc site.owner site.destination) site.pc state location
    exact ⟨head,ih (site.pc+10) chain.2 (fun later member => valid later (List.Mem.tail _ member))
      (fun later member => fields later (List.Mem.tail _ member))
      (StringStack.execute mode (StringStoreWrites.liftDword mode (StringRetarget.form mode site)) state) next⟩

end SmcTuring.Native.StringRetargetWrites
