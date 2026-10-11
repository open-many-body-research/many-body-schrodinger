import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Explicit bounded smooth approximations of a positive exponential. The
logistic saturation has relative derivative at most the requested exponent. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def saturatedExp (a L t : ℝ) : ℝ := L * Real.exp (a*t) / (L+Real.exp (a*t))

theorem saturatedExp_pos (a : ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    0 < saturatedExp a L t := by unfold saturatedExp; positivity

theorem saturatedExp_le_cap (a : ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    saturatedExp a L t ≤ L := by
  unfold saturatedExp
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg L]

theorem saturatedExp_le_exp (a : ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    saturatedExp a L t ≤ Real.exp (a*t) := by
  unfold saturatedExp
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg (Real.exp (a*t))]

theorem saturatedExp_contDiff (a : ℝ) {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ ∞ (saturatedExp a L) :=
  (contDiff_const.mul (contDiff_const.mul contDiff_id).exp).div
    (contDiff_const.add (contDiff_const.mul contDiff_id).exp) (fun t => by positivity)

theorem saturatedExp_hasDerivAt (a : ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasDerivAt (saturatedExp a L)
      (a * saturatedExp a L t * (L/(L+Real.exp (a*t)))) t := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (a*t)) (Real.exp (a*t)*a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).exp
  have h := (he.const_mul L).div (he.const_add L) (by positivity : L+Real.exp (a*t) ≠ 0)
  convert! h using 1
  unfold saturatedExp
  field_simp
  ring

theorem saturatedExp_deriv_bounds {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) (t : ℝ) :
    0 ≤ deriv (saturatedExp a L) t ∧
      deriv (saturatedExp a L) t ≤ a * saturatedExp a L t := by
  rw [(saturatedExp_hasDerivAt a hL t).deriv]
  have hr0 : 0 ≤ L/(L+Real.exp (a*t)) := by positivity
  have hr1 : L/(L+Real.exp (a*t)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_right (Real.exp_pos _).le)
  constructor
  · exact mul_nonneg (mul_nonneg ha (saturatedExp_pos a hL t).le) hr0
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1
      (mul_nonneg ha (saturatedExp_pos a hL t).le)

theorem saturatedExp_eq_div (a : ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    saturatedExp a L t = Real.exp (a*t) / (1+Real.exp (a*t)/L) := by
  have hden : L+Real.exp (a*t) ≠ 0 := by positivity
  unfold saturatedExp
  field_simp
  <;> ring

theorem saturatedExp_tendsto (a t : ℝ) :
    Tendsto (fun n : ℕ => saturatedExp a ((n : ℝ)+1) t) atTop (𝓝 (Real.exp (a*t))) := by
  have hsmall : Tendsto (fun n : ℕ => Real.exp (a*t)/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.exp (a*t))
  have h := (tendsto_const_nhds (x := Real.exp (a*t))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add hsmall) (by norm_num : (1 : ℝ)+0 ≠ 0)
  have heq : (fun n : ℕ => saturatedExp a ((n : ℝ)+1) t) =
      (fun n : ℕ => Real.exp (a*t)/(1+Real.exp (a*t)/((n : ℝ)+1))) :=
    funext (fun n => saturatedExp_eq_div a (by positivity) t)
  rw [heq]
  convert! h using 1 <;> simp

#print axioms saturatedExp_hasDerivAt
#print axioms saturatedExp_tendsto
end TheoremT.Continuum
