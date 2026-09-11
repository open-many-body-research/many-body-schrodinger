import CoulombCuspDerivativeLimits_v1
import PhysicalDistanceWeakLaplacian_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem coulombCuspHessian_trace (N : ℕ) (Z : ℝ) (x : Configuration N) :
    (∑ k : Coordinate N, coulombCuspHessian N Z (coordinateVector k) (coordinateVector k) x) =
      2*coulombPotential N Z x := by
  have hn : (∑ k : Coordinate N, ∑ i : Fin N,
      linearRadiusHessian (electronPositionCLM i) (coordinateVector k) (coordinateVector k) x) =
      ∑ i : Fin N, 2/‖position x i‖ := by
    rw [Finset.sum_comm]
    simp only [nuclear_linearRadiusHessian_trace]
  have hp : (∑ k : Coordinate N, ∑ i : Fin N,
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        linearRadiusHessian (pairDifferenceCLM i j) (coordinateVector k) (coordinateVector k) x) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        4/‖position x i-position x j‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact pair_linearRadiusHessian_trace i j (ne_of_lt (Finset.mem_filter.mp hj).2) x
  simp only [coulombCuspHessian,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hn,hp]
  simp only [coulombPotential,div_eq_mul_inv,← Finset.mul_sum]
  ring

#print axioms coulombCuspHessian_trace
end TheoremT.Continuum
