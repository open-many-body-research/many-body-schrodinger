import WeakDomainAlgebra_v2
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Multiplication by actual smooth compact cutoffs in the existing weak H¹
domain. This supplies a localization prerequisite, not a graph-density theorem. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

def cutoffMul {N : ℕ} (χ : Configuration N → ℝ) (hχ : Continuous χ)
    (hcχ : HasCompactSupport χ) (f : SpatialL2 N) : SpatialL2 N :=
  ((Lp.memLp f).smul (hχ.memLp_top_of_hasCompactSupport hcχ volume)).toLp
    (fun x => χ x • f x)

theorem cutoffMul_ae {N : ℕ} (χ : Configuration N → ℝ) (hχ : Continuous χ)
    (hcχ : HasCompactSupport χ) (f : SpatialL2 N) :
    cutoffMul χ hχ hcχ f =ᵐ[volume] (fun x => χ x • f x) :=
  MemLp.coeFn_toLp _

theorem integral_test_cutoff {N : ℕ} (χ : Configuration N → ℝ) (hχ : Continuous χ)
    (hcχ : HasCompactSupport χ) (f : SpatialL2 N) (φ : Configuration N → ℝ) :
    (∫ x, φ x • cutoffMul χ hχ hcχ f x) = (∫ x, (φ x * χ x) • f x) := by
  apply integral_congr_ae
  filter_upwards [cutoffMul_ae χ hχ hcχ f] with x hx
  rw [hx, mul_smul]

theorem weakPartial_cutoff {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (χ : Configuration N → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    WeakPartial (cutoffMul χ hχ.continuous hcχ f)
      (cutoffMul χ hχ.continuous hcχ g +
        cutoffMul (fun x => fderiv ℝ χ x (coordinateVector k))
          ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hcχ.fderiv_apply ℝ (coordinateVector k)) f) k := by
  intro φ hφ hcφ
  have hdχ : Continuous (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hprod (x : Configuration N) :
      fderiv ℝ (fun y => φ y * χ y) x (coordinateVector k) =
        φ x * fderiv ℝ χ x (coordinateVector k) +
        fderiv ℝ φ x (coordinateVector k) * χ x := by
    have hh := (hφ.differentiable (by simp) x).hasFDerivAt.mul
      ((hχ.differentiable (by simp) x).hasFDerivAt)
    change HasFDerivAt (𝕜 := ℝ) (fun y => φ y * χ y) _ x at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hb : Integrable (fun x => (φ x * fderiv ℝ χ x (coordinateVector k)) • f x) :=
    test_integrable f (hφ.continuous.mul hdχ) hcφ.mul_right
  have hc : Integrable (fun x => (fderiv ℝ φ x (coordinateVector k) * χ x) • f x) :=
    test_integrable f (hdφ.mul hχ.continuous) (hcφ.fderiv_apply ℝ (coordinateVector k)).mul_right
  have htest := hg (fun x => φ x * χ x) (hφ.mul hχ) hcφ.mul_right
  have he : (∫ x, fderiv ℝ (fun y => φ y * χ y) x (coordinateVector k) • f x) =
      (∫ x, (φ x * fderiv ℝ χ x (coordinateVector k)) • f x) +
      (∫ x, (fderiv ℝ φ x (coordinateVector k) * χ x) • f x) := by
    simp_rw [hprod, add_smul]
    exact integral_add hb hc
  rw [he] at htest
  rw [integral_test_add _ _ hφ.continuous hcφ,
    integral_test_cutoff, integral_test_cutoff, integral_test_cutoff, htest]
  abel

theorem HasH1.cutoff {N : ℕ} {f : SpatialL2 N} (hf : HasH1 f)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    HasH1 (cutoffMul χ hχ.continuous hcχ f) := by
  obtain ⟨d, hd⟩ := hf
  refine ⟨fun k => cutoffMul χ hχ.continuous hcχ (d k) +
    cutoffMul (fun x => fderiv ℝ χ x (coordinateVector k))
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcχ.fderiv_apply ℝ (coordinateVector k)) f, ?_⟩
  intro k
  exact weakPartial_cutoff (hd k) χ hχ hcχ

#print axioms weakPartial_cutoff
#print axioms HasH1.cutoff
end TheoremT.Continuum
