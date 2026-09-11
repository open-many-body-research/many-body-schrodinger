import GenericCompactLaplacianTests_v1

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_compact_divergence_complex_test
    {ι : Type*} [Fintype ι] (f a : Lp ℂ 2 (volume : Measure E))
    (b : ι → Lp ℂ 2 (volume : Measure E)) (v : ι → E)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, Δ φ x • f x) = (∫ x, φ x • a x) - ∑ i, ∫ x, fderiv ℝ φ x (v i) • b i x)
    {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, Δ φ x • f x) = (∫ x, φ x • a x) - ∑ i, ∫ x, fderiv ℝ φ x (v i) • b i x := by
  have hr := h (Complex.reCLM ∘ φ) (Complex.reCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hi := h (Complex.imCLM ∘ φ) (Complex.imCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hre (x : E) : Δ (Complex.reCLM ∘ φ) x = (Δ φ x).re :=
    (hφ.of_le (by norm_num)).contDiffAt.laplacian_CLM_comp_left
  have him (x : E) : Δ (Complex.imCLM ∘ φ) x = (Δ φ x).im :=
    (hφ.of_le (by norm_num)).contDiffAt.laplacian_CLM_comp_left
  have hDre (x : E) (i : ι) : fderiv ℝ (Complex.reCLM ∘ φ) x (v i) = (fderiv ℝ φ x (v i)).re := by
    rw [fderiv_comp x Complex.reCLM.differentiableAt (hφ.differentiable (by simp) x)]
    simp
  have hDim (x : E) (i : ι) : fderiv ℝ (Complex.imCLM ∘ φ) x (v i) = (fderiv ℝ φ x (v i)).im := by
    rw [fderiv_comp x Complex.imCLM.differentiableAt (hφ.differentiable (by simp) x)]
    simp
  obtain ⟨hΔc,hΔs⟩ := generic_compact_laplacian_continuous_compact hφ hc
  have hD (i : ι) : Continuous (fun x => fderiv ℝ φ x (v i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [generic_integral_complex_test_split f hΔc hΔs,
    generic_integral_complex_test_split a hφ.continuous hc]
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, hre, him, hDre, hDim] at hr hi
  rw [hr,hi]
  simp_rw [generic_integral_complex_test_split (b _) (hD _) (hc.fderiv_apply ℝ _)]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]
  module

#print axioms generic_compact_divergence_complex_test
end TheoremT.Continuum
