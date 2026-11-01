import SaturatedExponential_v1

/-! Exact second derivative and relative bound for logistic exponential
saturation. The bound is uniform in the cap and uses no asymptotic argument. -/
noncomputable section
namespace TheoremT.Continuum

theorem saturatedExp_deriv_hasDerivAt (a : ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasDerivAt (deriv (saturatedExp a L))
      (a^2 * saturatedExp a L t * (L/(L+Real.exp (a*t))) *
        (2*(L/(L+Real.exp (a*t)))-1)) t := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (a*t)) (Real.exp (a*t)*a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).exp
  have hq := (hasDerivAt_const t L).div (he.const_add L)
    (by positivity : L+Real.exp (a*t) ≠ 0)
  have h := ((saturatedExp_hasDerivAt a hL t).const_mul a).mul hq
  have hfun : deriv (saturatedExp a L) = fun s =>
      a*saturatedExp a L s*(L/(L+Real.exp (a*s))) :=
    funext (fun s => (saturatedExp_hasDerivAt a hL s).deriv)
  rw [hfun]
  convert! h using 1
  unfold saturatedExp
  simp only [Pi.div_apply]
  field_simp
  ring

theorem saturatedExp_second_deriv_abs_le (a : ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    |deriv (deriv (saturatedExp a L)) t| ≤ a^2*saturatedExp a L t := by
  rw [(saturatedExp_deriv_hasDerivAt a hL t).deriv]
  have hq0 : 0 ≤ L/(L+Real.exp (a*t)) := by positivity
  have hq1 : L/(L+Real.exp (a*t)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_right (Real.exp_pos _).le)
  have hr : |2*(L/(L+Real.exp (a*t)))-1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hprod := mul_le_mul hq1 hr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [abs_mul,abs_of_nonneg (sq_nonneg a),
    abs_of_pos (saturatedExp_pos a hL t),abs_of_nonneg hq0]
  have h := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (sq_nonneg a) (saturatedExp_pos a hL t).le)
  nlinarith

#print axioms saturatedExp_deriv_hasDerivAt
#print axioms saturatedExp_second_deriv_abs_le
end TheoremT.Continuum
