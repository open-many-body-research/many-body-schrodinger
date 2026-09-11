import PhysicalDistanceLinearMaps_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem pairDifferenceCLM_basis {N : ℕ} (i j m : Fin N) (k : Fin 3) :
    pairDifferenceCLM i j (coordinateVector (m,k)) =
      (if m=i then TheoremT.Hardy.basisVector k else 0)-
        (if m=j then TheoremT.Hardy.basisVector k else 0) := by
  simp only [pairDifferenceCLM,ContinuousLinearMap.sub_apply,electronPositionCLM_basis]

theorem pairDifferenceCLM_column_norm_sq {N : ℕ} (i j m : Fin N) (hij : i ≠ j)
    (k : Fin 3) :
    ‖pairDifferenceCLM i j (coordinateVector (m,k))‖^2 =
      ‖electronPositionCLM i (coordinateVector (m,k))‖^2+
        ‖electronPositionCLM j (coordinateVector (m,k))‖^2 := by
  by_cases hi : m=i <;> by_cases hj : m=j
  · exact (hij (hi.symm.trans hj)).elim
  all_goals simp [pairDifferenceCLM_basis,electronPositionCLM_basis,hi,hj,hij,Ne.symm hij]

theorem pairDifferenceCLM_column_norm_sq_sum {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    (∑ k : Coordinate N, ‖pairDifferenceCLM i j (coordinateVector k)‖^2) = 6 := by
  have he (k : Coordinate N) := pairDifferenceCLM_column_norm_sq i j k.1 hij k.2
  simp_rw [he,Finset.sum_add_distrib,electronPositionCLM_column_norm_sq_sum]
  norm_num

theorem pairDifferenceCLM_column_inner_sq {N : ℕ} (i j m : Fin N) (hij : i ≠ j)
    (k : Fin 3) (y : Position) :
    (inner ℝ y (pairDifferenceCLM i j (coordinateVector (m,k))))^2 =
      (inner ℝ y (electronPositionCLM i (coordinateVector (m,k))))^2+
        (inner ℝ y (electronPositionCLM j (coordinateVector (m,k))))^2 := by
  by_cases hi : m=i <;> by_cases hj : m=j
  · exact (hij (hi.symm.trans hj)).elim
  all_goals simp [pairDifferenceCLM_basis,electronPositionCLM_basis,hi,hj,hij,Ne.symm hij]

theorem pairDifferenceCLM_column_inner_sq_sum {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (y : Position) :
    (∑ k : Coordinate N, (inner ℝ y (pairDifferenceCLM i j (coordinateVector k)))^2) =
      2*‖y‖^2 := by
  have he (k : Coordinate N) := pairDifferenceCLM_column_inner_sq i j k.1 hij k.2 y
  simp_rw [he,Finset.sum_add_distrib,electronPositionCLM_column_inner_sq_sum]
  ring

#print axioms pairDifferenceCLM_column_norm_sq_sum
#print axioms pairDifferenceCLM_column_inner_sq_sum
end TheoremT.Continuum
