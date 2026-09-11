import HydrogenSlicing_v1
import WeightedH1CoreTransfer_v1

/-! The sharp nuclear Coulomb uncertainty estimate for actual weak H¹ inputs.
There is no Sobolev approximation or slice-regularity premise in the final theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def electronCoordinateFinset {N : ℕ} (i : Fin N) : Finset (Coordinate N) :=
  Finset.univ.map ⟨fun k : Fin 3 => (i,k), fun _ _ h => congrArg Prod.snd h⟩

theorem sum_electronCoordinateFinset {N : ℕ} (i : Fin N) (a : Coordinate N → ℝ) :
    (∑ k ∈ electronCoordinateFinset i, a k) = ∑ k : Fin 3, a (i,k) := by
  simp only [electronCoordinateFinset, Finset.sum_map]
  rfl

theorem compact_nuclear_coulomb_core {N : ℕ} (i : Fin N) {t : ℝ} (ht : 0 < t)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    Integrable (fun x : Configuration N => ‖position x i‖⁻¹ * ‖u x‖^2) volume ∧
      (∫ x : Configuration N, ‖position x i‖⁻¹ * ‖u x‖^2) ≤
        (t/2)*(∫ x : Configuration N, ‖u x‖^2) + (2*t)⁻¹ *
          (∫ x : Configuration N, ∑ k ∈ electronCoordinateFinset i, ‖smoothPartial u k x‖^2) := by
  have h := compact_nuclear_coulomb_bound i ht (hu.of_le (by norm_num)) huc
  have hw : (fun x : Configuration N => ‖position x i‖⁻¹ * ‖u x‖^2) =
      (fun x : Configuration N => ‖u x‖^2 / ‖position x i‖) := by funext x; ring
  rw [hw]
  refine ⟨h.1, ?_⟩
  simp_rw [sum_electronCoordinateFinset, smoothPartial]
  change (∫ x : Configuration N, ‖u x‖^2 / ‖position x i‖) ≤
    (t/2)*(∫ x : Configuration N, ‖u x‖^2) +
      (2*t)⁻¹*(∫ x : Configuration N, electronGradientEnergy i u x)
  calc
    _ ≤ ((∫ x : Configuration N, electronGradientEnergy i u x) +
        t^2*(∫ x : Configuration N, ‖u x‖^2)) / (2*t) :=
      (le_div_iff₀ (by positivity : 0 < 2*t)).2 (by simpa only [mul_comm] using h.2)
    _ = _ := by field_simp [ht.ne']; ring

theorem weak_nuclear_coulomb_bound_pos {N : ℕ} (i : Fin N) {t : ℝ} (ht : 0 < t)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x : Configuration N => ‖f x‖^2 / ‖position x i‖) volume ∧
      2*t*(∫ x : Configuration N, ‖f x‖^2 / ‖position x i‖) ≤
        (∑ k : Fin 3, ‖d (i,k)‖^2) + t^2*‖f‖^2 := by
  have h := weighted_compact_core_bound_extends_weakH1
    (electronCoordinateFinset i) (fun x => ‖position x i‖⁻¹)
    (fun x => inv_nonneg.mpr (norm_nonneg _)) (t/2) (2*t)⁻¹
    (fun u hu huc => compact_nuclear_coulomb_core i ht hu huc) f d hd
  have hw : (fun x : Configuration N => ‖position x i‖⁻¹ * ‖f x‖^2) =
      (fun x : Configuration N => ‖f x‖^2 / ‖position x i‖) := by funext x; ring
  rw [hw, sum_electronCoordinateFinset] at h
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ 2*t*((t/2)*‖f‖^2 + (2*t)⁻¹*(∑ k : Fin 3, ‖d (i,k)‖^2)) :=
      mul_le_mul_of_nonneg_left h.2 (by positivity)
    _ = _ := by field_simp [ht.ne']; ring

/-- The exact one-electron directional completed-square estimate for arbitrary
actual weak-H¹ configuration inputs; it includes t=0 without a binding premise. -/
theorem weak_nuclear_coulomb_bound {N : ℕ} (i : Fin N) {t : ℝ} (ht : 0 ≤ t)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x : Configuration N => ‖f x‖^2 / ‖position x i‖) volume ∧
      2*t*(∫ x : Configuration N, ‖f x‖^2 / ‖position x i‖) ≤
        (∑ k : Fin 3, ‖d (i,k)‖^2) + t^2*‖f‖^2 := by
  rcases lt_or_eq_of_le ht with hpos | hz
  · exact weak_nuclear_coulomb_bound_pos i hpos f d hd
  · subst t
    refine ⟨(weak_nuclear_coulomb_bound_pos i (by norm_num : (0 : ℝ) < 1) f d hd).1, ?_⟩
    simp only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

#print axioms compact_nuclear_coulomb_core
#print axioms weak_nuclear_coulomb_bound
end TheoremT.Continuum
