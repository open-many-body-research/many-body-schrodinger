import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Elementary Hilbert-space variance and real inequalities used by the
unbounded-domain Temple proof. No operator-square expression occurs. -/
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_sub_real_smul_sq (x y : H) (t : ℝ) :
    ‖y - (t : ℂ) • x‖^2 =
      ‖y‖^2 - 2 * t * (inner ℂ x y).re + t^2 * ‖x‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, _root_.norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change ‖y‖^2 - 2 * ((t : ℂ) * inner ℂ y x).re + t^2 * ‖x‖^2 = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsym : (inner ℂ y x).re = (inner ℂ x y).re := inner_re_symm (𝕜 := ℂ) y x
  rw [hsym]
  ring

/-- The centered residual identity uses only one vector y, not an application
of an operator to y. Thus substituting y=Aψ does not require ψ∈D(A²). -/
theorem unit_variance_shift_identity (x y : H) (hx : ‖x‖ = 1) (E : ℝ) :
    ‖y - (E : ℂ) • x‖^2 =
      ‖y - ((inner ℂ x y).re : ℂ) • x‖^2 + ((inner ℂ x y).re - E)^2 := by
  rw [norm_sub_real_smul_sq, norm_sub_real_smul_sq, hx]
  ring

theorem gap_cauchy_numeric {δ s t u : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u)
    (hgap : δ * s ≤ t) (ht : 0 ≤ t) (hcs : t^2 ≤ s * u) : δ * t ≤ u := by
  by_cases hz : t = 0
  · simpa only [hz, mul_zero] using hu
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have ha := mul_le_mul_of_nonneg_left hcs hδ.le
    have hb := mul_le_mul_of_nonneg_right hgap hu
    nlinarith

#print axioms unit_variance_shift_identity
#print axioms gap_cauchy_numeric
end TheoremT.OperatorTheory
