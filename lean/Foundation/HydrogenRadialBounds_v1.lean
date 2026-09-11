import HydrogenRadialLp_v1

/-! Uniform algebraic domination for regularized radial first and second
derivative formulas. The statements do not assert that the formulas are
derivatives; that identification is a separate obligation. -/

noncomputable section
open MeasureTheory

namespace TheoremT.Continuum

theorem hydrogen_radial_first_coefficient_bound {Z r s a : ℝ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hrs : r ≤ s) (ha : |a| ≤ r) :
    |(-Z * a / s)| ≤ Z := by
  rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hZ, abs_of_pos hs]
  apply (div_le_iff₀ hs).2
  exact mul_le_mul_of_nonneg_left (ha.trans hrs) hZ

theorem hydrogen_radial_second_coefficient_bound {Z r s a b d : ℝ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (hrs : r ≤ s)
    (ha : |a| ≤ r) (hb : |b| ≤ r) (hd : |d| ≤ 1) :
    |Z ^ 2 * a * b / s ^ 2 - Z * d / s + Z * a * b / s ^ 3| ≤
      Z ^ 2 + 2 * Z / r := by
  have hs : 0 < s := hr.trans_le hrs
  have hab : |a| * |b| ≤ s ^ 2 := by
    calc
      |a| * |b| ≤ s * s := mul_le_mul (ha.trans hrs) (hb.trans hrs)
        (abs_nonneg b) hs.le
      _ = s ^ 2 := by ring
  have h1 : |Z ^ 2 * a * b / s ^ 2| ≤ Z ^ 2 := by
    simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hZ, abs_of_pos hs]
    apply (div_le_iff₀ (sq_pos_of_pos hs)).2
    nlinarith [mul_le_mul_of_nonneg_left hab (sq_nonneg Z)]
  have h2 : |Z * d / s| ≤ Z / r := by
    simp only [abs_div, abs_mul, abs_of_nonneg hZ, abs_of_pos hs]
    calc
      Z * |d| / s ≤ Z / s := div_le_div_of_nonneg_right
        (by nlinarith) hs.le
      _ ≤ Z / r := div_le_div_of_nonneg_left hZ hr hrs
  have h3 : |Z * a * b / s ^ 3| ≤ Z / r := by
    simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hZ, abs_of_pos hs]
    calc
      Z * |a| * |b| / s ^ 3 ≤ (Z * s ^ 2) / s ^ 3 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
        nlinarith [mul_le_mul_of_nonneg_left hab hZ]
      _ = Z / s := by field_simp
      _ ≤ Z / r := div_le_div_of_nonneg_left hZ hr hrs
  calc
    |Z ^ 2 * a * b / s ^ 2 - Z * d / s + Z * a * b / s ^ 3| ≤
        |Z ^ 2 * a * b / s ^ 2 - Z * d / s| + |Z * a * b / s ^ 3| := abs_add_le _ _
    _ ≤ |Z ^ 2 * a * b / s ^ 2| + |Z * d / s| + |Z * a * b / s ^ 3| := by
      gcongr
      exact abs_sub _ _
    _ ≤ Z ^ 2 + Z / r + Z / r := by gcongr
    _ = Z ^ 2 + 2 * Z / r := by ring

theorem hydrogen_norm_le_regularized_radius {N : ℕ} (x : Configuration N)
    {δ : ℝ} (hδ : 0 ≤ δ) : ‖x‖ ≤ Real.sqrt (‖x‖ ^ 2 + δ) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
  linarith

theorem hydrogen_exp_regularized_le {N : ℕ} (x : Configuration N)
    {Z δ : ℝ} (hZ : 0 ≤ Z) (hδ : 0 ≤ δ) :
    Real.exp (-Z * Real.sqrt (‖x‖ ^ 2 + δ)) ≤ Real.exp (-Z * ‖x‖) := by
  apply Real.exp_le_exp.mpr
  nlinarith [hydrogen_norm_le_regularized_radius x hδ]

theorem hydrogen_regularized_first_coefficient_bound {N : ℕ}
    (x : Configuration N) (k : Coordinate N) {Z δ : ℝ}
    (hZ : 0 ≤ Z) (hδ : 0 < δ) :
    |(-Z * x k / Real.sqrt (‖x‖ ^ 2 + δ))| ≤ Z := by
  apply hydrogen_radial_first_coefficient_bound hZ (Real.sqrt_pos.2 (by positivity))
    (hydrogen_norm_le_regularized_radius x hδ.le)
  exact_mod_cast PiLp.norm_apply_le x k

theorem hydrogen_regularized_second_coefficient_bound {N : ℕ}
    (x : Configuration N) (k l : Coordinate N) {Z δ : ℝ}
    (hZ : 0 ≤ Z) (hδ : 0 ≤ δ) (hx : x ≠ 0) :
    |Z ^ 2 * x k * x l / (Real.sqrt (‖x‖ ^ 2 + δ)) ^ 2 -
        Z * (if k = l then 1 else 0) / Real.sqrt (‖x‖ ^ 2 + δ) +
        Z * x k * x l / (Real.sqrt (‖x‖ ^ 2 + δ)) ^ 3| ≤
      Z ^ 2 + 2 * Z / ‖x‖ := by
  apply hydrogen_radial_second_coefficient_bound hZ (norm_pos_iff.mpr hx)
    (hydrogen_norm_le_regularized_radius x hδ)
  · exact_mod_cast PiLp.norm_apply_le x k
  · exact_mod_cast PiLp.norm_apply_le x l
  · split_ifs <;> norm_num

end TheoremT.Continuum
