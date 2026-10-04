import FormalMultilinearGeometricTranslation_v1
import ComplexPowerSeriesCenterDerivativeBound_v1

/-! All-order derivatives of the actual geometric formal-series sum.
Every constant is explicit, and the conclusion concerns actual complex
iterated Frechet derivatives at each point in the stated domain. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem formalMultilinearSeries_enorm_lt_radius_geometric
    (p : FormalMultilinearSeries ℂ E ℂ) {M D : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hp : ∀ n, ‖p n‖ ≤ M*D^n)
    (x : E) (hx : D*‖x‖ < 1) : ‖x‖ₑ < p.radius := by
  have hlocal (R : ℝ) (hR : 0 ≤ R) (hDR : D*R ≤ 1) (hxR : ‖x‖ < R) :
      ‖x‖ₑ < p.radius := by
    apply lt_of_lt_of_le _ (formalMultilinearSeries_radius_geometric p hM hD hR hDR hp)
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [norm_nonneg x])).mpr hxR
  by_cases hD0 : D = 0
  · exact hlocal (‖x‖+1) (by positivity) (by simp [hD0]) (by linarith)
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    apply hlocal D⁻¹ (inv_nonneg.mpr hD) (by simp [hD0])
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hDp).mpr (by simpa [mul_comm] using hx)

theorem formalMultilinearSeries_sum_geometric_derivative_bound
    (p : FormalMultilinearSeries ℂ E ℂ) {M D : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hp : ∀ n, ‖p n‖ ≤ M*D^n)
    (x : E) (hx : D*‖x‖ < 1) (k : ℕ) :
    ‖iteratedFDeriv ℂ k p.sum x‖ ≤
      (k.factorial : ℝ)*(M*D^k/(1-D*‖x‖)^(k+1)) := by
  have hxr := formalMultilinearSeries_enorm_lt_radius_geometric p hM hD hp x hx
  have hf := (p.hasFPowerSeriesOnBall (lt_of_le_of_lt (by positivity) hxr)).changeOrigin hxr
  have hd := complex_powerSeries_norm_iteratedFDeriv_le_factorial_coeff hf k
  simp only [zero_add] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left
    (formalMultilinearSeries_changeOrigin_geometric_bound p hM hD hp x hx k) (Nat.cast_nonneg _))

theorem formalMultilinearSeries_sum_half_domain_factorial_bound
    (p : FormalMultilinearSeries ℂ E ℂ) {M D : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hp : ∀ n, ‖p n‖ ≤ M*D^n)
    (x : E) (hx : D*‖x‖ ≤ 1/2) (k : ℕ) :
    ‖iteratedFDeriv ℂ k p.sum x‖ ≤ (2*M)*(2*D)^k*(k.factorial : ℝ) := by
  have hx1 : D*‖x‖ < 1 := by linarith
  have hinv : (1-D*‖x‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hcoeff : M*D^k/(1-D*‖x‖)^(k+1) ≤ (2*M)*(2*D)^k := by
    calc
      _ = M*D^k*((1-D*‖x‖)⁻¹)^(k+1) := by rw [div_eq_mul_inv,inv_pow]
      _ ≤ M*D^k*(2:ℝ)^(k+1) := by gcongr
      _ = _ := by rw [pow_succ,mul_pow]; ring
  exact (formalMultilinearSeries_sum_geometric_derivative_bound p hM hD hp x hx1 k).trans
    (by simpa [mul_comm,mul_left_comm,mul_assoc] using
      mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg k.factorial))

end TheoremT.Continuum
