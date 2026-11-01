import FormalMultilinearGeometricAnalytic_v1
import Mathlib.Analysis.SpecificLimits.Normed

/-! Polynomially many homogeneous blocks do not reduce the geometric
analytic radius. The multiplicity is the exact binomial coefficient
(n+d choose d), not an unspecified cost or assumed convergence profile. -/
noncomputable section
set_option autoImplicit false
open scoped NNReal ENNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem formalMultilinearSeries_radius_binomial_geometric
    (p : FormalMultilinearSeries ℂ E ℂ) (d : ℕ) {M D R : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hR : 0 ≤ R) (hDR : D*R < 1)
    (hp : ∀ n, ‖p n‖ ≤ M*((n+d).choose d : ℝ)*D^n) :
    ENNReal.ofReal R ≤ p.radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal hR]
  apply p.le_radius_of_summable
  have hq : ‖D*R‖ < 1 := by rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hD hR)]; exact hDR
  have hgeom := (summable_choose_mul_geometric_of_norm_lt_one d hq).mul_left M
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hR n))
    (fun n => ?_) hgeom
  change ‖p n‖*R^n ≤ M*((n+d).choose d * (D*R)^n)
  calc
    _ ≤ (M*((n+d).choose d : ℝ)*D^n)*R^n :=
      mul_le_mul_of_nonneg_right (hp n) (pow_nonneg hR n)
    _ = _ := by rw [mul_pow]; ring

theorem formalMultilinearSeries_analyticOnNhd_binomial_geometric
    (p : FormalMultilinearSeries ℂ E ℂ) (d : ℕ) {M D : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hp : ∀ n, ‖p n‖ ≤ M*((n+d).choose d : ℝ)*D^n) :
    AnalyticOnNhd ℂ p.sum {x : E | D*‖x‖ < 1} := by
  intro x hx
  apply p.analyticOnNhd x
  apply mem_eball_zero_iff.mpr
  have hlocal (R : ℝ) (hR : 0 ≤ R) (hDR : D*R < 1) (hxR : ‖x‖ < R) :
      ‖x‖ₑ < p.radius := by
    apply lt_of_lt_of_le _ (formalMultilinearSeries_radius_binomial_geometric p d hM hD hR hDR hp)
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [norm_nonneg x])).mpr hxR
  by_cases hD0 : D = 0
  · exact hlocal (‖x‖+1) (by positivity) (by simp [hD0]) (by linarith)
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    have hxi : ‖x‖ < 1/D := (lt_div_iff₀ hDp).mpr (by simpa [mul_comm] using hx)
    obtain ⟨R,hxR,hRD⟩ := exists_between hxi
    exact hlocal R ((norm_nonneg x).trans hxR.le)
      (by simpa [mul_comm] using (lt_div_iff₀ hDp).mp hRD) hxR

end TheoremT.Continuum
