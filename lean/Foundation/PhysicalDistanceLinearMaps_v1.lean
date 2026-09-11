import NuclearHardySlicing_v2

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def electronPositionCLM {N : ℕ} (i : Fin N) : Configuration N →L[ℝ] Position :=
  (ContinuousLinearMap.fst ℝ Position (SpectatorConfiguration i)).comp
    (configurationProductEquiv i).toContinuousLinearMap

theorem electronPositionCLM_apply {N : ℕ} (i : Fin N) (x : Configuration N) :
    electronPositionCLM i x = position x i := rfl

def pairDifferenceCLM {N : ℕ} (i j : Fin N) : Configuration N →L[ℝ] Position :=
  electronPositionCLM i-electronPositionCLM j

theorem pairDifferenceCLM_apply {N : ℕ} (i j : Fin N) (x : Configuration N) :
    pairDifferenceCLM i j x = position x i-position x j := rfl

theorem electronPositionCLM_basis {N : ℕ} (i j : Fin N) (k : Fin 3) :
    electronPositionCLM i (coordinateVector (j,k)) =
      if j=i then TheoremT.Hardy.basisVector k else 0 := by
  rw [electronPositionCLM_apply]
  by_cases h : j=i
  · subst j
    ext a
    simp [position,coordinateVector,TheoremT.Hardy.basisVector]
  · ext a
    simp [position,coordinateVector,TheoremT.Hardy.basisVector,h,Ne.symm h]

theorem electronPositionCLM_column_norm_sq_sum {N : ℕ} (i : Fin N) :
    (∑ k : Coordinate N, ‖electronPositionCLM i (coordinateVector k)‖^2) = 3 := by
  rw [Fintype.sum_prod_type]
  simp [electronPositionCLM_basis,apply_ite,Finset.sum_ite_irrel,TheoremT.Hardy.basisVector]

theorem electronPositionCLM_column_inner_sq_sum {N : ℕ} (i : Fin N) (y : Position) :
    (∑ k : Coordinate N, (inner ℝ y (electronPositionCLM i (coordinateVector k)))^2) = ‖y‖^2 := by
  rw [Fintype.sum_prod_type]
  simp [electronPositionCLM_basis,apply_ite,Finset.sum_ite_irrel,TheoremT.Hardy.basisVector,
    EuclideanSpace.inner_single_right,← EuclideanSpace.real_norm_sq_eq]

#print axioms electronPositionCLM_column_norm_sq_sum
#print axioms electronPositionCLM_column_inner_sq_sum
end TheoremT.Continuum
