import HardyLaplacianCore_v3

/-! Compact core identities expressed in the actual L² quotient Hilbert space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem compact_energy_identity_L2 {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N) (lap : SpatialL2 N)
    (hf : (f : Configuration N → ℂ) =ᵐ[volume] u)
    (hd : ∀ k, (d k : Configuration N → ℂ) =ᵐ[volume] smoothPartial u k)
    (hlap : (lap : Configuration N → ℂ) =ᵐ[volume] smoothLaplacian u) :
    (∑ k : Coordinate N, ‖d k‖^2) = -inner ℝ f lap := by
  have he : (∑ k : Coordinate N, ‖d k‖^2) =
      (∫ x, ∑ k : Coordinate N, ‖smoothPartial u k x‖^2) := by
    rw [integral_finset_sum Finset.univ (fun k _ => smooth_partial_sq_integrable hu huc k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [spatialL2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [hd k] with x hx
    rw [hx]
  rw [he, compact_laplacian_energy_identity hu huc, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hf, hlap] with x hx hx'
  rw [hx, hx']

theorem compact_complex_ibp_L2 {N : ℕ} {u v : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (huc : HasCompactSupport u)
    (f g df dg : SpatialL2 N) (k : Coordinate N)
    (hf : (f : Configuration N → ℂ) =ᵐ[volume] u)
    (hg : (g : Configuration N → ℂ) =ᵐ[volume] v)
    (hdf : (df : Configuration N → ℂ) =ᵐ[volume] smoothPartial u k)
    (hdg : (dg : Configuration N → ℂ) =ᵐ[volume] smoothPartial v k) :
    inner ℂ f dg = -inner ℂ df g := by
  rw [L2.inner_def, L2.inner_def]
  have hleft : (∫ x, inner ℂ (f x) (dg x)) =
      (∫ x, star (u x) * smoothPartial v k x) := by
    apply integral_congr_ae
    filter_upwards [hf, hdg] with x hx hx'
    rw [hx, hx', RCLike.inner_apply']
    rfl
  have hright : (∫ x, inner ℂ (df x) (g x)) =
      (∫ x, star (smoothPartial u k x) * v x) := by
    apply integral_congr_ae
    filter_upwards [hdf, hg] with x hx hx'
    rw [hx, hx', RCLike.inner_apply']
    rfl
  rw [hleft, hright]
  exact compact_complex_partial_ibp hu hv huc k

#print axioms compact_energy_identity_L2
#print axioms compact_complex_ibp_L2
end TheoremT.Continuum
