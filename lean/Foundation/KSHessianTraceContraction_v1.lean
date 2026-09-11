import KSMapHessian_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def ksTargetBasis (i : Fin 3) : Position := WithLp.toLp 2 (Pi.single i 1)

theorem ksMap_fderiv_basis_expansion (y : KSSpace) (k : Fin 4) :
    fderiv ℝ ksMap y (ksBasis k) =
      ∑ i : Fin 3, ksJacobian y i k • ksTargetBasis i := by
  ext i
  rw [ksMap_fderiv_coordinate]
  simp [ksBasis,ksTargetBasis,Pi.single_apply]

theorem ks_bilinear_trace_contraction {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : Position →L[ℝ] Position →L[ℝ] G) (y : KSSpace) :
    (∑ k : Fin 4, B (fderiv ℝ ksMap y (ksBasis k)) (fderiv ℝ ksMap y (ksBasis k))) =
      (4*‖y‖^2) • ∑ i : Fin 3, B (ksTargetBasis i) (ksTargetBasis i) := by
  simp_rw [ksMap_fderiv_basis_expansion,map_sum,map_smul]
  simp only [sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul,Finset.smul_sum,smul_smul]
  calc
    (∑ k : Fin 4, ∑ i : Fin 3, ∑ j : Fin 3,
      (ksJacobian y i k*ksJacobian y j k) • B (ksTargetBasis j) (ksTargetBasis i)) =
        ∑ i : Fin 3, ∑ j : Fin 3, (∑ k : Fin 4, ksJacobian y i k*ksJacobian y j k) •
          B (ksTargetBasis j) (ksTargetBasis i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_smul]
    _ = ∑ i : Fin 3, (4*‖y‖^2) • B (ksTargetBasis i) (ksTargetBasis i) := by
      simp_rw [ksJacobian_row_orthogonality]
      simp [ite_smul,Finset.smul_sum]

#print axioms ksMap_fderiv_basis_expansion
#print axioms ks_bilinear_trace_contraction
end TheoremT.Continuum
