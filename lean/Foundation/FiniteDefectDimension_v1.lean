import FiniteDefectCauchy_v1
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! An actual finite-dimensional comparison bounds the dimension of every
linear domain subspace whose Rayleigh values stay strictly below its threshold.
This includes degenerate eigenspaces. No uniqueness assumption is introduced. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.OperatorTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem finite_defect_low_subspace_dimension
    (m : ℕ) (A : E →ₗ.[ℂ] E) (l : E →L[ℂ] (Fin m → ℂ))
    (β C r : ℝ) (hrβ : r < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖^2 ≤
      (inner ℂ (x : E) (A x)).re + C * ‖l (x : E)‖^2)
    (S : Submodule ℂ A.domain)
    (hupper : ∀ x : S,
      (inner ℂ ((x : A.domain) : E) (A (x : A.domain))).re ≤
        r * ‖((x : A.domain) : E)‖^2) :
    FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ m := by
  let L : S →ₗ[ℂ] (Fin m → ℂ) :=
    l.toLinearMap.comp (A.domain.subtype.comp S.subtype)
  have hinj : Function.Injective L := by
    intro x y hxy
    let w : S := x-y
    have hLw : l ((w : A.domain) : E) = 0 := by
      change L (x-y) = 0
      rw [map_sub,hxy,sub_self]
    have hlow := hform (w : A.domain)
    have hup := hupper w
    rw [hLw,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] at hlow
    have hnorm : ‖((w : A.domain) : E)‖ = 0 := by
      have hn := norm_nonneg ((w : A.domain) : E)
      apply le_antisymm ?_ hn
      by_contra hnot
      have hs := mul_lt_mul_of_pos_right hrβ (sq_pos_of_pos (lt_of_not_ge hnot))
      exact (not_lt_of_ge (hlow.trans hup)) hs
    have hw : w = 0 := Subtype.ext (Subtype.ext (norm_eq_zero.mp hnorm))
    exact sub_eq_zero.mp hw
  have hfinite : FiniteDimensional ℂ S := FiniteDimensional.of_injective L hinj
  refine ⟨hfinite,?_⟩
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using hdim

/-- The literal eigenspace is a subspace of the actual operator domain. -/
def partialEigenspace (A : E →ₗ.[ℂ] E) (r : ℝ) : Submodule ℂ A.domain :=
  LinearMap.ker (A.toFun - (r : ℂ) • A.domain.subtype)

theorem finite_defect_eigenspace_dimension
    (m : ℕ) (A : E →ₗ.[ℂ] E) (l : E →L[ℂ] (Fin m → ℂ))
    (β C r : ℝ) (hrβ : r < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖^2 ≤
      (inner ℂ (x : E) (A x)).re + C * ‖l (x : E)‖^2) :
    FiniteDimensional ℂ (partialEigenspace A r) ∧
      Module.finrank ℂ (partialEigenspace A r) ≤ m := by
  apply finite_defect_low_subspace_dimension m A l β C r hrβ hform
  intro x
  have heig : A (x : A.domain) = (r : ℂ) • ((x : A.domain) : E) := by
    have hx := x.property
    simpa only [partialEigenspace,LinearMap.mem_ker,LinearMap.sub_apply,
      LinearMap.smul_apply,Submodule.subtype_apply,sub_eq_zero,
      LinearPMap.toFun_eq_coe] using hx
  rw [heig,inner_smul_right,inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

#print axioms finite_defect_low_subspace_dimension
#print axioms finite_defect_eigenspace_dimension
end TheoremT.OperatorTheory
