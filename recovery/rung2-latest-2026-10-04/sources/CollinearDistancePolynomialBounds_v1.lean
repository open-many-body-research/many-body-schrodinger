import PairDistancePolynomialBounds_v1

/-! Explicit polynomial numerator bounds for the noncollision collinear
distance chart. All variables are literal complex scalars and all centers
and radii are displayed. No quotient, chart equality or neighborhood is
assumed or constructed in this algebra module. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem collinear_complex_square_deviation {R δ : ℝ} (hR : 0≤R) (hδ : 0≤δ)
    {a c : ℂ} (hc : ‖c‖≤R) (ha : ‖a-c‖≤δ) :
    ‖a^2-c^2‖ ≤ δ*(2*R+δ) := by
  have hsum : ‖a+c‖≤2*R+δ := by
    calc
      _ = ‖(a-c)+(c+c)‖ := by congr 1; ring
      _ ≤ ‖a-c‖+‖c+c‖ := norm_add_le _ _
      _ ≤ δ+(R+R) := add_le_add ha ((norm_add_le c c).trans (add_le_add hc hc))
      _ = 2*R+δ := by ring
  calc
    _ = ‖(a-c)*(a+c)‖ := by congr 1; ring
    _ = ‖a-c‖*‖a+c‖ := norm_mul _ _
    _ ≤ δ*(2*R+δ) := mul_le_mul ha hsum (norm_nonneg _) hδ

theorem collinear_distance_numerator_bound {r0 σ u0 δ : ℝ}
    (hr0 : 0≤r0) (hσ : 0<σ) (hu0 : 0≤u0) (hδ : 0≤δ)
    {z0 r s u : ℂ} (hz0 : ‖z0‖≤r0)
    (hr : ‖r-(r0 : ℂ)‖≤δ) (hs : ‖s-(σ : ℂ)‖≤δ) (hu : ‖u-(u0 : ℂ)‖≤δ) :
    ‖(r^2-(r0 : ℂ)^2)+(s^2-(σ : ℂ)^2)-(u^2-(u0 : ℂ)^2)-2*z0*(s-(σ : ℂ))‖ ≤
      δ*(4*r0+2*σ+2*u0+3*δ) := by
  have hr2 := pair_distance_square_deviation hr0 hδ hr
  have hs2 := pair_distance_square_deviation hσ.le hδ hs
  have hu2 := pair_distance_square_deviation hu0 hδ hu
  have hz : ‖2*z0*(s-(σ : ℂ))‖ ≤ 2*r0*δ := by
    calc
      _ = 2*‖z0‖*‖s-(σ : ℂ)‖ := by simp only [norm_mul]; norm_num
      _ ≤ 2*r0*δ := mul_le_mul
        (mul_le_mul_of_nonneg_left hz0 (by norm_num)) hs (norm_nonneg _) (by positivity)
  calc
    _ ≤ ‖(r^2-(r0 : ℂ)^2)+(s^2-(σ : ℂ)^2)-(u^2-(u0 : ℂ)^2)‖+
        ‖2*z0*(s-(σ : ℂ))‖ := norm_sub_le _ _
    _ ≤ ‖r^2-(r0 : ℂ)^2‖+‖s^2-(σ : ℂ)^2‖+‖u^2-(u0 : ℂ)^2‖+
        ‖2*z0*(s-(σ : ℂ))‖ := by
      have hsub := norm_sub_le ((r^2-(r0 : ℂ)^2)+(s^2-(σ : ℂ)^2)) (u^2-(u0 : ℂ)^2)
      have hadd := norm_add_le (r^2-(r0 : ℂ)^2) (s^2-(σ : ℂ)^2)
      linarith
    _ ≤ δ*(4*r0+2*σ+2*u0+3*δ) := by nlinarith

theorem collinear_distance_numerator_bound_coarse {r0 σ u0 δ : ℝ}
    (hr0 : 0≤r0) (hσ : 0<σ) (hu0 : 0≤u0) (hδ : 0≤δ) (hsmall : δ≤σ/4)
    {z0 r s u : ℂ} (hz0 : ‖z0‖≤r0)
    (hr : ‖r-(r0 : ℂ)‖≤δ) (hs : ‖s-(σ : ℂ)‖≤δ) (hu : ‖u-(u0 : ℂ)‖≤δ) :
    ‖(r^2-(r0 : ℂ)^2)+(s^2-(σ : ℂ)^2)-(u^2-(u0 : ℂ)^2)-2*z0*(s-(σ : ℂ))‖ ≤
      6*(r0+σ+u0)*δ := by
  have hi : 4*r0+2*σ+2*u0+3*δ ≤ 6*(r0+σ+u0) := by linarith
  calc
    _ ≤ δ*(4*r0+2*σ+2*u0+3*δ) :=
      collinear_distance_numerator_bound hr0 hσ hu0 hδ hz0 hr hs hu
    _ ≤ δ*(6*(r0+σ+u0)) := mul_le_mul_of_nonneg_left hi hδ
    _ = 6*(r0+σ+u0)*δ := by ring

end TheoremT.Continuum
