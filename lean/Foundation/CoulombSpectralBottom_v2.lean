import HardyCoulombSelfAdjoint_v1
import VariationalOperatorBridge_v2

/-! The actual continuum variational energy is finite and is the least real
point of the ordinary bounded-inverse spectrum. Exclusion of nonreal spectrum
is a separate generic result, not silently built into this statement. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.Continuum

theorem coulomb_variational_energy_least_real_spectrum (N : ℕ) (Z : ℝ) :
    IsLeast {t : ℝ | (t : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum
      (coulombPartialOperator N Z)} (variationalGroundEnergy N Z).toReal :=
  TheoremT.OperatorTheory.isLeast_real_spectrum_of_greatest_lower_bound
    (coulombPartialOperator N Z) (coulombPartialOperator_selfAdjoint N Z)
    (variational_energy_isGreatest_operatorLowerBounds N Z)

theorem coulomb_variational_energy_mem_spectrum (N : ℕ) (Z : ℝ) :
    ((variationalGroundEnergy N Z).toReal : ℂ) ∈
      TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z) :=
  (coulomb_variational_energy_least_real_spectrum N Z).1

/-- An explicit finite real energy, retaining equality to the original EReal
definition, the actual self-adjoint operator, and its independently defined H²
domain. No ground vector, binding or gap occurs in the statement. -/
theorem coulomb_selfAdjoint_H2_finite_spectral_bottom (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (coulombPartialOperator N Z) ∧
    ((coulombPartialOperator N Z).domain : Set (FermionicSpace N)) =
      {ψ | ∀ σ, HasH2 (ψ.val σ)} ∧
    ∃ E : ℝ, variationalGroundEnergy N Z = (E : EReal) ∧
      IsLeast {t : ℝ | (t : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum
        (coulombPartialOperator N Z)} E := by
  refine ⟨coulombPartialOperator_selfAdjoint N Z,
    coulombPartialOperator_domain_eq_H2 N Z,
    (variationalGroundEnergy N Z).toReal, ?_,
    coulomb_variational_energy_least_real_spectrum N Z⟩
  obtain ⟨hbot,htop⟩ := variational_ground_energy_finite N Z
  exact (EReal.coe_toReal hbot htop).symm

theorem coulombPartialOperator_closed (N : ℕ) (Z : ℝ) :
    (coulombPartialOperator N Z).IsClosed :=
  (coulombPartialOperator_selfAdjoint N Z).isClosed

#print axioms coulomb_variational_energy_least_real_spectrum
#print axioms coulomb_selfAdjoint_H2_finite_spectral_bottom
#print axioms coulombPartialOperator_closed
end TheoremT.Continuum
