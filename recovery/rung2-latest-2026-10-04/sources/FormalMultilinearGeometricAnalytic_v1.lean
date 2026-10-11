import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Tactic

/-! An actual formal multilinear series with geometrically bounded coefficient
norms is analytic in any complex normed domain where D * norm(x) < 1.
The D = 0 case is included rather than represented by an inverse-zero radius. -/
noncomputable section
set_option autoImplicit false
open scoped NNReal ENNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem formalMultilinearSeries_radius_geometric
    (p : FormalMultilinearSeries ℂ E ℂ) {M D R : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hR : 0 ≤ R) (hDR : D*R ≤ 1)
    (hp : ∀ n, ‖p n‖ ≤ M*D^n) :
    ENNReal.ofReal R ≤ p.radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal hR]
  apply p.le_radius_of_bound M
  intro n
  change ‖p n‖ * R^n ≤ M
  calc
    _ ≤ (M*D^n)*R^n := mul_le_mul_of_nonneg_right (hp n) (pow_nonneg hR n)
    _ = M*(D*R)^n := by rw [mul_pow]; ring
    _ ≤ M*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (mul_nonneg hD hR) hDR) hM
    _ = M := mul_one M

theorem formalMultilinearSeries_analyticAt_geometric
    (p : FormalMultilinearSeries ℂ E ℂ) {M D : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hp : ∀ n, ‖p n‖ ≤ M*D^n) (X : E) (hX : D*‖X‖ < 1) :
    AnalyticAt ℂ p.sum X := by
  have hlocal (R : ℝ) (hR : 0 ≤ R) (hDR : D*R ≤ 1) (hXR : ‖X‖ < R) :
      AnalyticAt ℂ p.sum X := by
    apply p.analyticOnNhd X
    apply mem_eball_zero_iff.mpr
    apply lt_of_lt_of_le _ (formalMultilinearSeries_radius_geometric p hM hD hR hDR hp)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith [norm_nonneg X]) |>.mpr hXR
  by_cases hD0 : D = 0
  · exact hlocal (‖X‖+1) (by positivity) (by simp [hD0]) (by linarith)
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    apply hlocal D⁻¹ (inv_nonneg.mpr hD) (by simp [hD0])
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hDp).mpr (by simpa [mul_comm] using hX)

theorem formalMultilinearSeries_analyticOnNhd_geometric
    (p : FormalMultilinearSeries ℂ E ℂ) {M D : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hp : ∀ n, ‖p n‖ ≤ M*D^n) :
    AnalyticOnNhd ℂ p.sum {X : E | D*‖X‖ < 1} :=
  fun X hX => formalMultilinearSeries_analyticAt_geometric p hM hD hp X hX

end TheoremT.Continuum
