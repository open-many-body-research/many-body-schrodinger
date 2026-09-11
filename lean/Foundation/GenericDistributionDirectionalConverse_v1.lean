import GenericFirstCutoffPairing_v1

/-!
Actual L2 weak directional derivatives defined by all real compact smooth tests
are exactly their tempered-distribution derivatives. The converse uses explicit
scaled cutoffs and L2 pairing convergence, without a test-density assumption.
-/
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_compact_directional_complex_test
    {f g : Lp ℂ 2 (volume : Measure E)} {v : E} (h : WeakL2Directional f g v)
    {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x • g x) = -(∫ x, fderiv ℝ φ x v • f x) := by
  have hr := h (Complex.reCLM ∘ φ) (Complex.reCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hi := h (Complex.imCLM ∘ φ) (Complex.imCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hDre (x : E) : fderiv ℝ (Complex.reCLM ∘ φ) x v = (fderiv ℝ φ x v).re := by
    rw [fderiv_comp x Complex.reCLM.differentiableAt (hφ.differentiable (by simp) x)]
    simp
  have hDim (x : E) : fderiv ℝ (Complex.imCLM ∘ φ) x v = (fderiv ℝ φ x v).im := by
    rw [fderiv_comp x Complex.imCLM.differentiableAt (hφ.differentiable (by simp) x)]
    simp
  have hD : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [generic_integral_complex_test_split g hφ.continuous hc,
    generic_integral_complex_test_split f hD (hc.fderiv_apply ℝ v)]
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, hDre, hDim] at hr hi
  rw [hr,hi]
  simp only [smul_neg, neg_add_rev]
  abel

theorem distribution_directional_of_weakL2Directional
    {f g : Lp ℂ 2 (volume : Measure E)} {v : E} (h : WeakL2Directional f g v) :
    ∂_{v} (f : 𝓢'(E,ℂ)) = (g : 𝓢'(E,ℂ)) := by
  ext φ
  let u (n : ℕ) : E → ℂ := fun x => genericScaledCutoff E ((n : ℝ)+1) x • φ x
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) := (genericScaledCutoff_contDiff E _).smul φ.smooth'
  have hc (n : ℕ) : HasCompactSupport (u n) := (genericScaledCutoff_compact E (by positivity)).smul_right
  have heq (n : ℕ) : (∫ x, u n x * g x) = -(∫ x, fderiv ℝ (u n) x v * f x) := by
    simpa only [smul_eq_mul] using generic_compact_directional_complex_test h (hu n) (hc n)
  have hleft := generic_schwartz_cutoff_pairing_limit φ g
  have hright := (generic_schwartz_cutoff_first_pairing_limit φ f v).neg
  have hright' : Tendsto (fun n : ℕ => ∫ x, u n x*g x) atTop
      (𝓝 (-(∫ x, fderiv ℝ φ x v*f x))) :=
    hright.congr' (Eventually.of_forall (fun n => (heq n).symm))
  have hlim := tendsto_nhds_unique hleft hright'
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.neg_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, neg_smul, smul_eq_mul, neg_mul, integral_neg]
  exact hlim.symm

theorem weakL2Directional_iff_distribution
    {f g : Lp ℂ 2 (volume : Measure E)} {v : E} :
    WeakL2Directional f g v ↔ ∂_{v} (f : 𝓢'(E,ℂ)) = (g : 𝓢'(E,ℂ)) :=
  ⟨distribution_directional_of_weakL2Directional, weakL2Directional_of_distribution⟩

#print axioms distribution_directional_of_weakL2Directional
#print axioms weakL2Directional_iff_distribution
end TheoremT.Continuum
