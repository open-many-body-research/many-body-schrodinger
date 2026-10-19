import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Explicit complex polynomial estimates for the pair-distance chart.
These inequalities concern the literal complex variables and their norms;
they neither select a square-root branch nor assume a chart identity. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum

theorem pair_distance_square_deviation {σ δ : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    {r : ℂ} (hr : ‖r - (σ : ℂ)‖ ≤ δ) :
    ‖r^2 - (σ : ℂ)^2‖ ≤ δ * (2*σ+δ) := by
  have hsum : ‖r + (σ : ℂ)‖ ≤ 2*σ+δ := by
    calc
      _ = ‖(r - (σ : ℂ)) + ((σ : ℂ) + (σ : ℂ))‖ := by congr 1; ring
      _ ≤ ‖r - (σ : ℂ)‖ + ‖(σ : ℂ) + (σ : ℂ)‖ := norm_add_le _ _
      _ ≤ δ + (σ+σ) := by
        apply add_le_add hr
        calc
          _ ≤ ‖(σ : ℂ)‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
          _ = σ+σ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ]
      _ = 2*σ+δ := by ring
  calc
    _ = ‖(r - (σ : ℂ)) * (r + (σ : ℂ))‖ := by congr 1; ring
    _ = ‖r - (σ : ℂ)‖ * ‖r + (σ : ℂ)‖ := norm_mul _ _
    _ ≤ δ * (2*σ+δ) := mul_le_mul hr hsum (norm_nonneg _) hδ

theorem pair_distance_center_polynomial_bound {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : δ ≤ σ/16)
    {r s u : ℂ} (hr : ‖r - (σ : ℂ)‖ ≤ δ)
    (hs : ‖s - (σ : ℂ)‖ ≤ δ) (hu : ‖u‖ ≤ δ) :
    ‖(r^2+s^2)/2-u^2/4-(σ : ℂ)^2‖ ≤ 3*σ*δ := by
  have hr2 := pair_distance_square_deviation (le_of_lt hσ) hδ hr
  have hs2 := pair_distance_square_deviation (le_of_lt hσ) hδ hs
  have hu2 : ‖u‖^2 ≤ δ^2 := by nlinarith [norm_nonneg u]
  have hδ2 : δ^2 ≤ σ*δ/16 := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hsmall)]
  calc
    _ = ‖((r^2-(σ : ℂ)^2)+(s^2-(σ : ℂ)^2))/2-u^2/4‖ := by congr 1; ring
    _ ≤ ‖((r^2-(σ : ℂ)^2)+(s^2-(σ : ℂ)^2))/2‖ + ‖u^2/4‖ := norm_sub_le _ _
    _ = ‖(r^2-(σ : ℂ)^2)+(s^2-(σ : ℂ)^2)‖/2 + ‖u‖^2/4 := by
      simp only [norm_div,norm_pow]
      norm_num
    _ ≤ (‖r^2-(σ : ℂ)^2‖+‖s^2-(σ : ℂ)^2‖)/2 + ‖u‖^2/4 := by
      have htri := norm_add_le (r^2-(σ : ℂ)^2) (s^2-(σ : ℂ)^2)
      linarith
    _ ≤ 3*σ*δ := by nlinarith

theorem pair_distance_center_polynomial_strict {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : δ ≤ σ/16)
    {r s u : ℂ} (hr : ‖r - (σ : ℂ)‖ ≤ δ)
    (hs : ‖s - (σ : ℂ)‖ ≤ δ) (hu : ‖u‖ ≤ δ) :
    ‖(r^2+s^2)/2-u^2/4-(σ : ℂ)^2‖ < σ^2/4 := by
  have h := pair_distance_center_polynomial_bound hσ hδ hsmall hr hs hu
  have hp := mul_le_mul_of_nonneg_left hsmall (le_of_lt hσ)
  nlinarith [sq_pos_of_pos hσ]

theorem pair_distance_difference_squares_bound {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : δ ≤ σ/16)
    {r s : ℂ} (hr : ‖r - (σ : ℂ)‖ ≤ δ)
    (hs : ‖s - (σ : ℂ)‖ ≤ δ) :
    ‖r^2-s^2‖ ≤ 5*σ*δ := by
  have hr2 := pair_distance_square_deviation (le_of_lt hσ) hδ hr
  have hs2 := pair_distance_square_deviation (le_of_lt hσ) hδ hs
  have hδ2 : δ^2 ≤ σ*δ/16 := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hsmall)]
  calc
    _ = ‖(r^2-(σ : ℂ)^2)-(s^2-(σ : ℂ)^2)‖ := by congr 1; ring
    _ ≤ ‖r^2-(σ : ℂ)^2‖+‖s^2-(σ : ℂ)^2‖ := norm_sub_le _ _
    _ ≤ 5*σ*δ := by nlinarith

theorem pair_distance_axis_quotient_bound {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : δ ≤ σ/16)
    {r s t : ℂ} (hr : ‖r - (σ : ℂ)‖ ≤ δ)
    (hs : ‖s - (σ : ℂ)‖ ≤ δ) (ht : σ/2 ≤ ‖t‖) :
    ‖(r^2-s^2)/(2*t)‖ ≤ 5*δ := by
  have hdiff := pair_distance_difference_squares_bound hσ hδ hsmall hr hs
  have ht0 : 0 < 2*‖t‖ := by linarith
  simp only [norm_div,norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ ht0).mpr
  nlinarith [mul_le_mul_of_nonneg_left ht hδ]

theorem pair_distance_transverse_polynomial_bound {δ : ℝ} (hδ : 0 ≤ δ)
    {u z : ℂ} (hu : ‖u‖ ≤ δ) (hz : ‖z‖ ≤ 5*δ) :
    ‖u^2-z^2‖ ≤ 26*δ^2 := by
  have hu2 : ‖u‖^2 ≤ δ^2 := by nlinarith [norm_nonneg u]
  have hz2 : ‖z‖^2 ≤ 25*δ^2 := by nlinarith [norm_nonneg z]
  calc
    _ ≤ ‖u^2‖+‖z^2‖ := norm_sub_le _ _
    _ = ‖u‖^2+‖z‖^2 := by simp only [norm_pow]
    _ ≤ 26*δ^2 := by nlinarith

end TheoremT.Continuum
