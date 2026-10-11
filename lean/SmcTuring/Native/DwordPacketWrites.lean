module
public import SmcTuring.Native.DwordPackets
public import SmcTuring.Native.MixedLocatedWrites
public import SmcTuring.Native.StringMixedWrites

public section
namespace SmcTuring.Native.DwordPacketWrites

/-- The actual payload is read from the current instruction. Its value
cannot change the static complete four-byte relocated destination. -/
theorem code_write (mode : Mode) (codeStart codeEnd : Nat) (site : DwordPackets.Site) (valid : DwordPackets.Valid mode site)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode site.pc)
    (inside : codeStart≤site.target ∧ site.target+4≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd
      (StringStoreWrites.liftDword mode (StringDwordArithmetic.canonical mode (DwordPackets.live mode site state.principal.memory))) state := by
  have size : DwordArithmetic.length (DwordPackets.raw site.operation (DwordCode.get state.principal.memory (site.pc+6)))=DwordPackets.size site := by
    cases site with | mk pc op target => cases op <;> rfl
  have field:=MixedLocatedWrites.field mode codeStart codeEnd site.pc site.target
    (DwordPackets.raw site.operation (DwordCode.get state.principal.memory (site.pc+6))) state.principal
    (by cases site with | mk pc op target => cases op <;> rfl) entry
    (by simpa only [size] using valid.2.2) valid.2.1 inside
  exact StringMixedWrites.code_write mode codeStart codeEnd (.arithmetic (DwordPackets.live mode site state.principal.memory)) state field

theorem owned (mode : Mode) (codeStart codeEnd : Nat) (sites : List DwordPackets.Site) (start : Nat)
    (chain : DwordPackets.Contiguous start sites) (valid : ∀ site∈sites,DwordPackets.Valid mode site)
    (fields : ∀ site∈sites,codeStart≤site.target ∧ site.target+4≤codeEnd)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd ((DwordPackets.program mode sites state.principal).map (StringStoreWrites.liftDword mode)) state := by
  induction sites generalizing start state with
  | nil => trivial
  | cons site sites ih =>
    have ready:=valid site (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have first:=code_write mode codeStart codeEnd site ready state location (fields site (List.Mem.head _))
    have next : (DwordPackets.execute mode site state.principal).pc=Arithmetic.encodeNat mode (site.pc+DwordPackets.size site) := by
      rw [DwordPackets.effect mode site ready state.principal location]
    constructor
    · exact first
    · change StringWrites.OwnedRun mode codeStart codeEnd _
        (StringDword.execute mode (StringDwordArithmetic.canonical mode (DwordPackets.live mode site state.principal.memory)) state)
      rw [StringDwordArithmetic.execute]
      exact ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
        (fun later member => fields later (List.Mem.tail _ member))
        {state with principal:=DwordPackets.execute mode site state.principal} next

theorem run (mode : Mode) (sites : List DwordPackets.Site) (state : StringExecution.State mode) :
    StringWrites.run mode ((DwordPackets.program mode sites state.principal).map (StringStoreWrites.liftDword mode)) state=
      {state with principal:=DwordPackets.finish mode sites state.principal} := by
  induction sites generalizing state with
  | nil => rfl
  | cons site sites ih =>
    change StringWrites.run mode _
      (StringDword.execute mode (StringDwordArithmetic.canonical mode (DwordPackets.live mode site state.principal.memory)) state)=_
    rw [StringDwordArithmetic.execute]
    exact ih {state with principal:=DwordPackets.execute mode site state.principal}

end SmcTuring.Native.DwordPacketWrites
