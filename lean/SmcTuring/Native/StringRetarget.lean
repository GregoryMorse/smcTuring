module
public import SmcTuring.Native.StringDword
public import SmcTuring.Native.DwordRetargetSequence

public section
namespace SmcTuring.Native.StringRetarget
open DwordRetargetSequence

@[expose] def form (mode : Mode) (site : Site) := StringDword.store mode
  (Relocation.memoryDisp mode (site.pc+10) (site.owner+2)) (DwordRetarget.printed mode site.pc site.owner site.destination)
@[expose] def program (mode : Mode) (sites : List Site) := sites.map (form mode)
@[expose] def advance (mode : Mode) (site : Site) (state : StringExecution.State mode) :=
  { state with principal := DwordRetarget.patched mode site.pc site.owner site.destination state.principal }
@[expose] def finish (mode : Mode) (sites : List Site) (state : StringExecution.State mode) :=
  { state with principal := DwordRetargetSequence.finish mode sites state.principal }

theorem execution (mode : Mode) (site : Site) (state : StringExecution.State mode) :
    StringDword.execute mode (form mode site) state = advance mode site state := by
  rw [form,StringDword.store_execute]
  rfl

/-- The existing retargeting packets execute in the same decoder and state
as TRANSFERDATA. Every later fetch is derived by the exact prior store frame. -/
theorem trace (mode : Mode) (sites : List Site) (start : Nat) (chain : Contiguous start sites)
    (valid : ∀ site ∈ sites, Valid mode site) (outside : OutsideCodes sites)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (intact : Intact mode sites state.principal.memory) :
    StringDword.Trace mode state (program mode sites) (finish mode sites state) := by
  induction sites generalizing start state with
  | nil => exact .nil state
  | cons site sites ih =>
    have ready := valid site (List.mem_cons_self ..)
    have pcFits := ready.1
    have ownerFits := ready.2.1
    have location : state.principal.pc = Arithmetic.encodeNat mode site.pc := by rw [chain.1]; exact entry
    have firstFetch : StringDword.fetch mode state.principal.memory state.principal.pc.toNat = some (form mode site) := by
      rw [location,Arithmetic.encode_nat_toNat mode _ (by omega)]
      exact StringDword.store_encoding mode _ _ _ _ (intact site (List.mem_cons_self ..))
    have firstEffect := DwordRetarget.patch_effect mode site.pc site.owner site.destination state.principal location ready.2.2 (by omega)
    have next : (advance mode site state).principal.pc = Arithmetic.encodeNat mode (site.pc+10) := by
      rw [advance,firstEffect]
    have restIntact : Intact mode sites (advance mode site state).principal.memory := by
      intro reader member
      rw [advance,firstEffect,DwordRetargetSequence.bytes_frame _ site _ reader.pc 10
        (outside site (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))]
      exact intact reader (List.mem_cons_of_mem _ member)
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader readerMember => outside writer (List.mem_cons_of_mem _ member)
        reader (List.mem_cons_of_mem _ readerMember)) (advance mode site state) next restIntact
    have last : StringDword.Trace mode (StringDword.execute mode (form mode site) state)
        (program mode sites) (finish mode (site::sites) state) := by
      rw [execution]
      exact rest
    exact .step firstFetch last

end SmcTuring.Native.StringRetarget
