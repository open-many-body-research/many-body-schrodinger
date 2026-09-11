import GenericWeakL2Algebra_v1

/-! Bounded smooth real multipliers on actual weak directional L2 derivatives
in arbitrary finite Euclidean dimension. These maps are analytic objects, not
executable integration algorithms. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def genericBoundedRealMul (χ : E → ℝ) (hχ : MemLp χ (⊤ : ENNReal) volume)
    (f : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure E) :=
  ((Lp.memLp f).smul hχ).toLp (fun x => χ x • f x)

theorem genericBoundedRealMul_ae (χ : E → ℝ)
    (hχ : MemLp χ (⊤ : ENNReal) volume) (f : Lp ℂ 2 (volume : Measure E)) :
    genericBoundedRealMul χ hχ f =ᵐ[volume] (fun x => χ x • f x) :=
  MemLp.coeFn_toLp _

theorem integral_test_genericBoundedRealMul (χ : E → ℝ)
    (hχ : MemLp χ (⊤ : ENNReal) volume) (f : Lp ℂ 2 (volume : Measure E)) (φ : E → ℝ) :
    (∫ x, φ x • genericBoundedRealMul χ hχ f x) = (∫ x, (φ x * χ x) • f x) := by
  apply integral_congr_ae
  filter_upwards [genericBoundedRealMul_ae χ hχ f] with x hx
  rw [hx,mul_smul]

theorem weakL2Directional_genericBoundedRealMul {f g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hg : WeakL2Directional f g v) (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ (⊤ : ENNReal) volume)
    (hdm : MemLp (fun x => fderiv ℝ χ x v) (⊤ : ENNReal) volume) :
    WeakL2Directional (genericBoundedRealMul χ hm f)
      (genericBoundedRealMul χ hm g +
        genericBoundedRealMul (fun x => fderiv ℝ χ x v) hdm f) v := by
  intro φ hφ hcφ
  have hdχ : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hprod (x : E) :
      fderiv ℝ (fun y => φ y * χ y) x v =
        φ x * fderiv ℝ χ x v +
        fderiv ℝ φ x v * χ x := by
    have hh := (hφ.differentiable (by simp) x).hasFDerivAt.mul
      ((hχ.differentiable (by simp) x).hasFDerivAt)
    change HasFDerivAt (𝕜 := ℝ) (fun y => φ y * χ y) _ x at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hb : Integrable (fun x => (φ x * fderiv ℝ χ x v) • f x) :=
    generic_real_test_integrable f (hφ.continuous.mul hdχ) hcφ.mul_right
  have hc : Integrable (fun x => (fderiv ℝ φ x v * χ x) • f x) :=
    generic_real_test_integrable f (hdφ.mul hχ.continuous) (hcφ.fderiv_apply ℝ v).mul_right
  have htest := hg (fun x => φ x * χ x) (hφ.mul hχ) hcφ.mul_right
  have he : (∫ x, fderiv ℝ (fun y => φ y * χ y) x v • f x) =
      (∫ x, (φ x * fderiv ℝ χ x v) • f x) +
      (∫ x, (fderiv ℝ φ x v * χ x) • f x) := by
    simp_rw [hprod,add_smul]
    exact integral_add hb hc
  rw [he] at htest
  rw [generic_integral_test_add _ _ hφ.continuous hcφ,
    integral_test_genericBoundedRealMul,integral_test_genericBoundedRealMul,
    integral_test_genericBoundedRealMul,htest]
  abel


#print axioms weakL2Directional_genericBoundedRealMul
end TheoremT.Continuum
