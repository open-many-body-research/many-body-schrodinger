import FiniteDefectSpectralAttainment_v1
import FiniteDefectDimension_v1
import CoulombRankOneBranch_v1

/-! A conditional physical ground-attainment theorem permitting degeneracy.
The explicit finite-dimensional form comparison yields an actual ground
eigenvector and a bound on the dimension of the actual ground eigenspace.
It does not imply a rank-one complement bound or a unique ground vector. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.Continuum

theorem coulomb_finite_defect_ground (N m : ℕ) (Z : ℝ)
    (l : FermionicSpace N →L[ℂ] (Fin m → ℂ)) (β C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : (coulombPartialOperator N Z).domain,
      β * ‖(x : FermionicSpace N)‖^2 ≤
        (inner ℂ (x : FermionicSpace N) (coulombPartialOperator N Z x)).re +
          C * ‖l (x : FermionicSpace N)‖^2)
    (trial : (coulombPartialOperator N Z).domain)
    (htrial : ‖(trial : FermionicSpace N)‖ = 1)
    (htrialβ : (inner ℂ (trial : FermionicSpace N)
      (coulombPartialOperator N Z trial)).re < β) :
    (variationalGroundEnergy N Z).toReal < β ∧
    (∃ g : (coulombPartialOperator N Z).domain,
      ‖(g : FermionicSpace N)‖ = 1 ∧
      coulombPartialOperator N Z g =
        ((variationalGroundEnergy N Z).toReal : ℂ) • (g : FermionicSpace N)) ∧
    FiniteDimensional ℂ (TheoremT.OperatorTheory.partialEigenspace
      (coulombPartialOperator N Z) (variationalGroundEnergy N Z).toReal) ∧
    Module.finrank ℂ (TheoremT.OperatorTheory.partialEigenspace
      (coulombPartialOperator N Z) (variationalGroundEnergy N Z).toReal) ≤ m := by
  have heβ : (variationalGroundEnergy N Z).toReal < β :=
    (coulomb_ground_energy_le_domain_rayleigh N Z trial htrial).trans_lt htrialβ
  have hatt := TheoremT.OperatorTheory.selfAdjoint_spectral_eigenvector_of_finite_defect
    m (coulombPartialOperator N Z) (coulombPartialOperator_selfAdjoint N Z)
    l β C hC hbound (variationalGroundEnergy N Z).toReal
    (coulomb_variational_energy_mem_spectrum N Z) heβ
  have hdim := TheoremT.OperatorTheory.finite_defect_eigenspace_dimension
    m (coulombPartialOperator N Z) l β C (variationalGroundEnergy N Z).toReal heβ hbound
  exact ⟨heβ,hatt,hdim.1,hdim.2⟩

#print axioms coulomb_finite_defect_ground
end TheoremT.Continuum
