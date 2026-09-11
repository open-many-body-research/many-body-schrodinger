import ContinuumFoundation_v1
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! The actual Euclidean four-to-three Kustaanheimo–Stiefel polynomial map.
The convention matches KS_WEAK_REMOVABILITY_v1.md, equation K11. -/
noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

abbrev KSSpace := EuclideanSpace ℝ (Fin 4)

def ksMap (y : KSSpace) : Position := WithLp.toLp 2
  ![2*(y 0*y 2+y 1*y 3),2*(y 1*y 2-y 0*y 3),y 0^2+y 1^2-y 2^2-y 3^2]

def ksJacobian (y : KSSpace) : Matrix (Fin 3) (Fin 4) ℝ :=
  ![![2*y 2,2*y 3,2*y 0,2*y 1],
    ![-2*y 3,2*y 2,2*y 1,-2*y 0],
    ![2*y 0,2*y 1,-2*y 2,-2*y 3]]

theorem ksMap_norm_sq (y : KSSpace) : ‖ksMap y‖^2=(‖y‖^2)^2 := by
  simp [EuclideanSpace.real_norm_sq_eq,ksMap,Fin.sum_univ_succ]
  ring

theorem ksMap_norm (y : KSSpace) : ‖ksMap y‖=‖y‖^2 :=
  (sq_eq_sq₀ (norm_nonneg _) (sq_nonneg _)).mp (ksMap_norm_sq y)

theorem ksMap_eq_zero_iff (y : KSSpace) : ksMap y=0 ↔ y=0 := by
  rw [← norm_eq_zero,ksMap_norm,sq_eq_zero_iff,norm_eq_zero]

theorem ksJacobian_row_orthogonality (y : KSSpace) (i j : Fin 3) :
    (∑ k : Fin 4, ksJacobian y i k*ksJacobian y j k) =
      if i=j then 4*‖y‖^2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ksJacobian,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ] <;> ring

theorem ksMap_contDiff : ContDiff ℝ ∞ ksMap := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : KSSpace => 2*(x 0*x 2+x 1*x 3))
    fun_prop
  · change ContDiff ℝ ∞ (fun x : KSSpace => 2*(x 1*x 2-x 0*x 3))
    fun_prop
  · change ContDiff ℝ ∞ (fun x : KSSpace => x 0^2+x 1^2-x 2^2-x 3^2)
    fun_prop

#print axioms ksMap_norm
#print axioms ksMap_eq_zero_iff
#print axioms ksJacobian_row_orthogonality
#print axioms ksMap_contDiff
end TheoremT.Continuum
