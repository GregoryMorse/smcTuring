module
public import SmcTuring.Appendix.DwordComparisonTail
public import SmcTuring.Native.MixedLocatedWrites

public section
namespace SmcTuring.Appendix.DwordComparisonTailWrites
open Native DwordComparisonTail

theorem instruction (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (index : Fin 4) (state : Execution.State mode)
    (entry : state.pc=Arithmetic.encodeNat mode (layout.start+offset index))
    (scalarInside : codeStart≤layout.scalar ∧ layout.scalar+4≤codeEnd)
    (maskInside : codeStart≤layout.mask ∧ layout.mask+4≤codeEnd) :
    codeStart≤(MixedDword.address mode (.arithmetic (form mode layout symbol index)) state).toNat ∧
      (MixedDword.address mode (.arithmetic (form mode layout symbol index)) state).toNat+4≤codeEnd := by
  have fits : target layout index<2^(8*mode.wordBytes) := by
    have scalar:=valid.scalarFits;have mask:=valid.maskFits
    fin_cases index <;> simp only [target] <;> omega
  have inside : codeStart≤target layout index ∧ target layout index+4≤codeEnd := by
    fin_cases index <;> first | exact scalarInside | exact maskInside
  exact MixedLocatedWrites.field mode codeStart codeEnd _ _ (raw symbol index) state
    (by fin_cases index <;> rfl) entry
    (by have range:=valid.ranges index;fin_cases index <;> exact range) fits inside

/-- All SUB/NEG/SBB/NOT stores own their actual complete fields. Future PCs
are consequences of the reached instructions rather than premises. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (valid : Valid mode layout)
    (symbol : Dword) (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode (layout.start+10))
    (scalarInside : codeStart≤layout.scalar ∧ layout.scalar+4≤codeEnd)
    (maskInside : codeStart≤layout.mask ∧ layout.mask+4≤codeEnd) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd)
      (program mode layout symbol) state := by
  have a:=instruction mode codeStart codeEnd layout valid symbol 0 state entry scalarInside maskInside
  have b:=instruction mode codeStart codeEnd layout valid symbol 1 (subState mode layout symbol state)
    (sub_pc mode layout valid symbol state entry) scalarInside maskInside
  have c:=instruction mode codeStart codeEnd layout valid symbol 2 (negState mode layout symbol state)
    (neg_pc mode layout valid symbol state entry) scalarInside maskInside
  have d:=instruction mode codeStart codeEnd layout valid symbol 3 (sbbState mode layout symbol state)
    (sbb_pc mode layout valid symbol state entry) scalarInside maskInside
  exact ⟨a,b,c,d,trivial⟩

end SmcTuring.Appendix.DwordComparisonTailWrites
