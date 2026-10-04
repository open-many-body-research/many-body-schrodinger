import CompactComplexOscillatorSquare_v1
import CompactSpectatorCutoffEnergy_v1
import EuclideanGrushinPrincipal_v1
import Mathlib.Tactic

/-! An explicit support-dependent Poincare estimate from the already proved
directional oscillator inequality. All integrals and derivatives are actual;
no Poincare or norm estimate is assumed. A single bounded coordinate on the
support suffices, so the result applies directly to the physical product boxes. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_slab_weight_integral_bound (L : E →L[ℝ] ℝ)
    {u : E → ℂ} (hu : Continuous u) (hc : HasCompactSupport u)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ x, u x ≠ 0 → |L x| ≤ R) :
    (∫ x, ‖L x • u x‖^2 ∂μ) ≤ R^2*(∫ x, ‖u x‖^2 ∂μ) := by
  have hi : Integrable (fun x => ‖u x‖^2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      compact_real_inner_integrable_general (μ := μ) hu hu hc
  have hwc : HasCompactSupport (fun x => L x • u x) := by
    apply hc.mono
    intro x hx hzero
    exact hx (by simp [hzero])
  have hw : Integrable (fun x => ‖L x • u x‖^2) μ := by
    have hcont : Continuous (fun x => L x • u x) := L.continuous.smul hu
    simpa only [real_inner_self_eq_norm_sq] using
      compact_real_inner_integrable_general (μ := μ) hcont hcont hwc
  calc
    (∫ x, ‖L x • u x‖^2 ∂μ) ≤ ∫ x, R^2*‖u x‖^2 ∂μ := by
      apply integral_mono hw (hi.const_mul _)
      intro x
      change ‖L x • u x‖^2 ≤ R^2*‖u x‖^2
      by_cases hx : u x = 0
      · simp [hx]
      · rw [norm_smul,mul_pow,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hs x hx) 2)
          (sq_nonneg _)
    _ = R^2*(∫ x, ‖u x‖^2 ∂μ) := integral_const_mul _ _

theorem compact_slab_poincare_integral (L : E →L[ℝ] ℝ) (v : E) (hLv : L v = 1)
    {u : E → ℂ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    {R : ℝ} (hR : 0 < R) (hs : ∀ x, u x ≠ 0 → |L x| ≤ R) :
    (∫ x, ‖u x‖^2 ∂μ) ≤ 4*R^2*(∫ x, ‖fderiv ℝ u x v‖^2 ∂μ) := by
  have hw := compact_slab_weight_integral_bound (μ := μ) L hu.continuous hc hR.le hs
  have ho := compact_complex_oscillator_directional_bound (μ := μ) L v hLv hu hc
    ((2*R^2)⁻¹)
  have ho2 := ho.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hw (sq_nonneg ((2*R^2)⁻¹))) _)
  have hm := mul_le_mul_of_nonneg_left ho2 (show 0 ≤ 2*R^2 from by positivity)
  have hRn : R ≠ 0 := ne_of_gt hR
  have hl : (2*R^2)*((2*R^2)⁻¹*(∫ x, ‖u x‖^2 ∂μ)) =
      (∫ x, ‖u x‖^2 ∂μ) := by field_simp
  have hr : (2*R^2)*((∫ x, ‖fderiv ℝ u x v‖^2 ∂μ)+
      ((2*R^2)⁻¹)^2*(R^2*(∫ x, ‖u x‖^2 ∂μ))) =
      (2*R^2)*(∫ x, ‖fderiv ℝ u x v‖^2 ∂μ)+(∫ x, ‖u x‖^2 ∂μ)/2 := by
    field_simp
    <;> ring
  rw [hl,hr] at hm
  linarith

theorem compact_product_y_slab_poincare
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (i : ι) {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    {R : ℝ} (hR : 0 < R) (hs : ∀ p, G p ≠ 0 → |p.1 i| ≤ R) :
    (∫ p, ‖G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) ≤
      4*R^2*(∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) := by
  letI := euclidean_product_volume_isAddHaar (ι := ι) (κ := κ)
  let L : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
  have hLv : L (oscillatorBasis i,0) = 1 := by simp [L,oscillatorBasis]
  exact compact_slab_poincare_integral (μ := (volume : Measure (EuclideanSpace ℝ ι)).prod volume)
    L (oscillatorBasis i,0) hLv (hG.of_le (by simp)) hc hR hs

end TheoremT.Continuum
