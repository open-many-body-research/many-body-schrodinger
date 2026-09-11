import FourierProductBridge_v1

/-!
Identification of a temperate multiplier from an L2 distributional output.
The product's L2 membership is concluded, not assumed.
No weak-derivative or physical Hamiltonian conclusion is asserted here.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace TheoremT.Continuum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ]

/-- A distributional multiplier equality with an L2 output identifies the
actual product almost everywhere; no product-integrability premise occurs. -/
theorem ae_smul_eq_of_toTemperedDistribution_eq
    (f g : Lp F 2 μ) {m : E → ℂ} (hm : m.HasTemperateGrowth)
    (heq : (g : 𝓢'(E, F)) = TemperedDistribution.smulLeftCLM F m f) :
    ∀ᵐ x ∂μ, g x = m x • f x := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp g).locallyIntegrable (by norm_num))
    (LocallyIntegrable.continuous_smul hm.1.continuous
      ((Lp.memLp f).locallyIntegrable (by norm_num)))
  intro φ hφ hcφ
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hcφ.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  have htest := congrArg (fun T : 𝓢'(E, F) => T (hc.toSchwartzMap hd)) heq
  have htest' : (∫ x, φ x • g x ∂μ) =
      ∫ x, (m x * (φ x : ℂ)) • f x ∂μ := by
    simpa [Lp.toTemperedDistribution_apply,
      TemperedDistribution.smulLeftCLM_apply_apply, hm, smul_smul, mul_comm] using htest
  rw [htest']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mul_comm, mul_smul, Complex.coe_smul]

/-- An L2 output for a distributional multiplier proves that the pointwise
product belongs to L2. This also applies to unbounded polynomial multipliers. -/
theorem memLp_smul_of_toTemperedDistribution_eq
    (f g : Lp F 2 μ) {m : E → ℂ} (hm : m.HasTemperateGrowth)
    (heq : (g : 𝓢'(E, F)) = TemperedDistribution.smulLeftCLM F m f) :
    MemLp (fun x => m x • f x) 2 μ :=
  MemLp.ae_eq (ae_smul_eq_of_toTemperedDistribution_eq f g hm heq) (Lp.memLp g)

#print axioms ae_smul_eq_of_toTemperedDistribution_eq
#print axioms memLp_smul_of_toTemperedDistribution_eq

end TheoremT.Continuum
