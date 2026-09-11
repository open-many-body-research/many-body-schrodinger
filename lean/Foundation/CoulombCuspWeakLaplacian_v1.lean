import PhysicalDistanceWeakLaplacian_v1
import LocalWeakLaplacian_v1

/-! Exact physical Coulomb cusp factor, all finite electron counts and real
charges. The weak identity is on the full configuration space, including
intersecting nuclear/pair collision strata. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def coulombCusp (N : ℕ) (Z : ℝ) (x : Configuration N) : ℝ :=
  -Z*(∑ i : Fin N, ‖position x i‖)+
    (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      ‖position x i-position x j‖)

theorem nuclear_radius_localWeakLaplacian {N : ℕ} (i : Fin N) :
    LocalWeakLaplacian (fun x => ‖position x i‖) (fun x => 2/‖position x i‖) := by
  refine ⟨(continuous_position i).norm.locallyIntegrable,?_,?_⟩
  · simpa only [Pi.smul_def,smul_eq_mul,div_eq_mul_inv] using (nuclear_inverse_locallyIntegrable i).smul (2:ℝ)
  · intro φ hφ hc
    exact nuclear_radius_weak_laplacian_test i hφ hc

theorem pair_radius_localWeakLaplacian {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    LocalWeakLaplacian (fun x => ‖position x i-position x j‖)
      (fun x => 4/‖position x i-position x j‖) := by
  refine ⟨((continuous_position i).sub (continuous_position j)).norm.locallyIntegrable,?_,?_⟩
  · simpa only [Pi.smul_def,smul_eq_mul,div_eq_mul_inv] using (pair_inverse_locallyIntegrable i j hij).smul (4:ℝ)
  · intro φ hφ hc
    exact pair_radius_weak_laplacian_test i j hij hφ hc

theorem coulombCusp_continuous (N : ℕ) (Z : ℝ) : Continuous (coulombCusp N Z) := by
  unfold coulombCusp position
  fun_prop

theorem coulombCusp_localWeakLaplacian (N : ℕ) (Z : ℝ) :
    LocalWeakLaplacian (coulombCusp N Z) (fun x => 2*coulombPotential N Z x) := by
  have hn := (LocalWeakLaplacian.finset_sum Finset.univ
    (fun i _ => nuclear_radius_localWeakLaplacian (N := N) i)).smul (-Z)
  have hp := (LocalWeakLaplacian.finset_sum Finset.univ (fun i _ =>
    LocalWeakLaplacian.finset_sum (Finset.univ.filter (fun j : Fin N => i<j))
      (fun j hj => pair_radius_localWeakLaplacian i j (ne_of_lt (Finset.mem_filter.mp hj).2)))).smul (1/2:ℝ)
  have h := hn.add hp
  change LocalWeakLaplacian (coulombCusp N Z)
    (fun x => -Z*(∑ i : Fin N, 2/‖position x i‖)+
      (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        4/‖position x i-position x j‖)) at h
  have he : (fun x : Configuration N => -Z*(∑ i : Fin N, 2/‖position x i‖)+
      (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        4/‖position x i-position x j‖)) = (fun x => 2*coulombPotential N Z x) := by
    funext x
    simp only [div_eq_mul_inv,← Finset.mul_sum,coulombPotential]
    ring
  rw [he] at h
  exact h

theorem coulombCusp_weak_laplacian_test (N : ℕ) (Z : ℝ)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x*(2*coulombPotential N Z x)) =
      ∫ x, realTestLaplacian φ x*coulombCusp N Z x :=
  (coulombCusp_localWeakLaplacian N Z).2.2 φ hφ hc

#print axioms coulombCusp_localWeakLaplacian
#print axioms coulombCusp_weak_laplacian_test
end TheoremT.Continuum
