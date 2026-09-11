import HardyLaplacianCore_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff RealInnerProductSpace
namespace TheoremT.Continuum

theorem smoothLaplacian_contDiff {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (smoothLaplacian u) := by
  apply ContDiff.sum
  intro k _
  exact smoothPartial_contDiff (smoothPartial_contDiff hu k) k

theorem smoothLaplacian_compact {N : ℕ} {u : Configuration N → ℂ}
    (huc : HasCompactSupport u) : HasCompactSupport (smoothLaplacian u) := by
  have he : smoothLaplacian u = ∑ k : Coordinate N, smoothPartial (smoothPartial u k) k := by
    funext x
    simp [smoothLaplacian]
  rw [he]
  exact HasCompactSupport.finset_sum (fun k _ =>
    smoothPartial_compact (smoothPartial_compact huc k) k)

theorem compact_laplacian_interpolation {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hf : MemLp u 2 volume) (hl : MemLp (smoothLaplacian u) 2 volume) :
    (∫ x, ∑ k : Coordinate N, ‖smoothPartial u k x‖^2) ≤
      ‖hf.toLp u‖ * ‖hl.toLp (smoothLaplacian u)‖ := by
  have he : inner ℝ (hf.toLp u) (hl.toLp (smoothLaplacian u)) =
      (∫ x, inner ℝ (u x) (smoothLaplacian u x)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hl.coeFn_toLp] with x hx hx'
    rw [hx, hx']
  rw [compact_laplacian_energy_identity hu huc, ← he]
  exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)

theorem norm_toLp_sq_eq_integral {N : ℕ} {u : Configuration N → ℂ}
    (hf : MemLp u 2 volume) : ‖hf.toLp u‖^2 = (∫ x, ‖u x‖^2) := by
  rw [spatialL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- The compact smooth Laplacian interpolation inequality, with every L²
membership premise discharged and all quantities expressed as physical integrals. -/
theorem compact_laplacian_interpolation_integrals {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    (∫ x, ∑ k : Coordinate N, ‖smoothPartial u k x‖^2)^2 ≤
      (∫ x, ‖u x‖^2) * (∫ x, ‖smoothLaplacian u x‖^2) := by
  have hf : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport huc
  have hl : MemLp (smoothLaplacian u) 2 volume :=
    (smoothLaplacian_contDiff hu).continuous.memLp_of_hasCompactSupport (smoothLaplacian_compact huc)
  have he := compact_laplacian_interpolation hu huc hf hl
  have hs := pow_le_pow_left₀
    (integral_nonneg (fun x => Finset.sum_nonneg (fun k _ => sq_nonneg _))) he 2
  simpa only [mul_pow, norm_toLp_sq_eq_integral] using hs

#print axioms compact_laplacian_interpolation
#print axioms compact_laplacian_interpolation_integrals
end TheoremT.Continuum
