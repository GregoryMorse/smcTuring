module
public import SmcTuring.CorrectedPaper
public section
namespace PalomarSMC
/-- Principal mathematical claims, using their existing individual proofs. -/
theorem mathematical_result : SmcTuring.CorrectedPaper.Unbounded ∧
    SmcTuring.CorrectedPaper.FourMov ∧ SmcTuring.CorrectedPaper.EffectiveInterpreter ∧
    SmcTuring.CorrectedPaper.Observations := by
  refine ⟨?_, SmcTuring.Dolan.Four.four_register_mov_certified_simulation,
    SmcTuring.SMC.Effective.terminal_search_pure_smc,
    SmcTuring.CorrectedPaper.observations⟩
  exact ⟨SmcTuring.SMC.Concrete.pure_infinitely_smc_universality,
    SmcTuring.SMC.Concrete.computably_initialized_unbounded_smc_witness⟩
end PalomarSMC
