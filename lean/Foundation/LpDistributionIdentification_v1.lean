import FourierProductIdentification_v1

noncomputable section
open MeasureTheory
open scoped SchwartzMap ContDiff ENNReal
namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ]

theorem ae_eq_of_Lp_temperedDistribution_eq {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (f : Lp ℂ p μ)
    (g : Lp ℂ q μ)
    (he : (f : 𝓢'(E,ℂ))=(g : 𝓢'(E,ℂ))) :
    (f : E → ℂ) =ᵐ[μ] g := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable (Fact.out : 1 ≤ p))
    ((Lp.memLp g).locallyIntegrable (Fact.out : 1 ≤ q))
  intro φ hφ hcφ
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hcφ.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  have hh := congrArg (fun T : 𝓢'(E,ℂ) => T (hc.toSchwartzMap hd)) he
  simpa [Lp.toTemperedDistribution_apply] using hh

#print axioms ae_eq_of_Lp_temperedDistribution_eq
end TheoremT.Continuum
