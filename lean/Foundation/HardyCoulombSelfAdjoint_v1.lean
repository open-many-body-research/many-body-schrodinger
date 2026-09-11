import HardyResolventError_v2
import SmallResolventError_v2
import FermionicClosed_v1

/-! Self-adjointness of the actual continuum fermionic Coulomb operator on
exactly the original weak H² domain, for every finite N and real charge Z.
No binding, spectral gap, ground-state uniqueness, or Theorem T is asserted. -/
noncomputable section
open MeasureTheory
open scoped LinearPMap
namespace TheoremT.Continuum

def coulombSelfAdjointShift (N : ℕ) (Z : ℝ) : ℝ :=
  1+8*(coulombFreeBoundConstant N Z)^2

theorem coulombSelfAdjointShift_pos (N : ℕ) (Z : ℝ) : 0 < coulombSelfAdjointShift N Z := by
  unfold coulombSelfAdjointShift
  positivity

theorem coulombFreeError_shift_norm_lt_one (N : ℕ) (Z : ℝ) :
    ‖coulombFreeError N Z (coulombSelfAdjointShift N Z) (coulombSelfAdjointShift_pos N Z)‖ < 1 := by
  apply lt_of_le_of_lt (norm_coulombFreeError_le N Z (coulombSelfAdjointShift_pos N Z))
  have hsqrt : 0 < Real.sqrt (2*coulombSelfAdjointShift N Z) :=
    Real.sqrt_pos.mpr (mul_pos (by norm_num) (coulombSelfAdjointShift_pos N Z))
  apply (div_lt_one hsqrt).mpr
  apply (Real.lt_sqrt (coulombFreeBoundConstant_nonneg N Z)).mpr
  unfold coulombSelfAdjointShift
  nlinarith [sq_nonneg (coulombFreeBoundConstant N Z)]

/-- Every finite-N atomic Coulomb operator defined by the original actual weak
fermionic graph is self-adjoint. The exact H² domain was established separately. -/
theorem coulombPartialOperator_selfAdjoint (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (coulombPartialOperator N Z) := by
  let μ := coulombSelfAdjointShift N Z
  have hμ : 0 < μ := coulombSelfAdjointShift_pos N Z
  apply TheoremT.OperatorTheory.selfAdjoint_of_small_resolvent_error
    (coulombPartialOperator N Z) μ (coulombPartialOperator_domain_dense N Z)
    (fun f g => (coulombPartialOperator_symmetric N Z f g).symm)
    (fermionicFreeResolvent N μ hμ) (coulombFreeError N Z μ hμ)
    (fermionicFreeResolvent_mem_domain N Z hμ)
  · exact coulombFreeError_identity N Z hμ
  · exact coulombFreeError_shift_norm_lt_one N Z

/-- Self-adjointness and exact equality with the independently specified weak
H² domain, with no extra analytic hypothesis. -/
theorem coulombPartialOperator_selfAdjoint_exact_H2 (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (coulombPartialOperator N Z) ∧
      ((coulombPartialOperator N Z).domain : Set (FermionicSpace N)) =
        {ψ | ∀ σ, HasH2 (ψ.val σ)} :=
  ⟨coulombPartialOperator_selfAdjoint N Z,coulombPartialOperator_domain_eq_H2 N Z⟩

#print axioms coulombFreeError_shift_norm_lt_one
#print axioms coulombPartialOperator_selfAdjoint
#print axioms coulombPartialOperator_selfAdjoint_exact_H2
end TheoremT.Continuum
