module
public import SmcTuring.Native.StringPCWindows
public import SmcTuring.Native.StringInstructionSizes

public section
namespace SmcTuring.Native.StringPCMargins
open MemoryRegion StringPCSteps

/-- Static space past the fragment endpoint covers short instructions'
classifier headers, without a future-PC or per-instruction margin premise. -/
theorem sequential (mode : Mode) (region : Region) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (pc : Nat)
    (straight : ∀ form∈forms,Sequential mode form)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (lower : region.lower≤pc) (upper : pc+total mode forms+3≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) : StringPCWindows.Run mode region forms state := by
  induction forms generalizing state pc with
  | nil => trivial
  | cons form rest ih =>
    have head:=straight form (List.Mem.head _)
    have tail:=fun later member=>straight later (List.Mem.tail _ member)
    have totalCons : total mode (form::rest)=size mode form+total mode rest := by simp only [total,List.map_cons,List.sum_cons]
    rw [totalCons] at upper
    refine ⟨?_,ih _ (pc+size mode form) tail (located_pc mode form state pc head entry) (by omega) (by omega)⟩
    unfold StringPCWindows.Envelope
    rw [entry,Arithmetic.encode_nat_toNat mode pc (by omega)]
    refine ⟨lower,?_⟩
    by_cases long : 3≤size mode form
    · rw [Nat.max_eq_right long];omega
    · rw [Nat.max_eq_left (by omega)];omega

/-- A short forward sequential span cannot hide a word-address wrap when
its independently proved endpoint follows its entry inside the word space. -/
theorem encode_span (mode : Mode) (pc count ending : Nat) (ordered : pc≤ending)
    (endFits : ending<2^(8*mode.wordBytes)) (short : count<2^(8*mode.wordBytes))
    (same : Arithmetic.encodeNat mode (pc+count)=Arithmetic.encodeNat mode ending) : pc+count=ending := by
  have equal:=congrArg (fun value : Word mode=>value.toNat) same
  simp only [Arithmetic.encodeNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt endFits] at equal
  by_cases small : pc+count<2^(8*mode.wordBytes)
  · rw [Nat.mod_eq_of_lt small] at equal
    exact equal
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at equal
    omega

theorem endpoint_span (mode : Mode) {state finish : StringExecution.State mode} {forms : List (StringStack.Form mode)}
    (actual : StringStack.Trace mode state forms finish) (pc ending : Nat)
    (straight : ∀ form∈forms,Sequential mode form)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc) (exit : finish.principal.pc=Arithmetic.encodeNat mode ending)
    (ordered : pc≤ending) (endFits : ending<2^(8*mode.wordBytes)) (short : total mode forms<2^(8*mode.wordBytes)) :
    pc+total mode forms=ending := by
  have progressed:=run_pc mode forms state straight
  rw [StringWrites.trace_run_eq mode actual,entry,exit] at progressed
  apply encode_span mode pc (total mode forms) ending ordered endFits short
  exact (BitVec.ofNat_add_ofNat _ _).symm.trans progressed.symm

/-- A positively derived actual trace and endpoint yield every reached PC
envelope from original placement and the trace's architectural size bound. -/
theorem of_trace (mode : Mode) (region : Region) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (pc ending : Nat) (straight : ∀ form∈forms,Sequential mode form)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc) (exit : finish.principal.pc=Arithmetic.encodeNat mode ending)
    (ordered : pc≤ending) (short : forms.length*15<2^(8*mode.wordBytes))
    (lower : region.lower≤pc) (upper : ending+3≤region.upper) (capacity : region.upper<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode region forms state := by
  have span:=endpoint_span mode actual pc ending straight entry exit ordered (by omega)
    (Nat.lt_of_le_of_lt (StringInstructionSizes.trace_total mode actual) short)
  apply sequential mode region forms state pc straight entry lower _ capacity
  rw [span]
  exact upper

end SmcTuring.Native.StringPCMargins
