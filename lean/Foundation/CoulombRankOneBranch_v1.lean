import RankOneSpectralAttainment_v1
import UnboundedEigenOrthogonality_v1
import CoulombSpectralFoundation_v3
import HardyRankOneTemple_v1

/-! Conditional physical ground-branch construction from an actual rank-one
form comparison and one actual strict trial. Attainment and spectral
separation are derived, not assumed. Hydrogen/Pauli comparison and the
explicit physical trial still need to instantiate the displayed premises. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.Continuum

theorem coulomb_ground_energy_le_domain_rayleigh (N : ℕ) (Z : ℝ)
    (ψ : (coulombPartialOperator N Z).domain) (hψ : ‖(ψ : FermionicSpace N)‖ = 1) :
    (variationalGroundEnergy N Z).toReal ≤
      (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re := by
  have hb := (variational_energy_isGreatest_operatorLowerBounds N Z).1 ψ
  change (variationalGroundEnergy N Z).toReal * ‖(ψ : FermionicSpace N)‖^2 ≤
    (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re at hb
  simpa only [hψ,one_pow,mul_one] using hb

theorem coulomb_rankOne_ground_branch (N : ℕ) (Z : ℝ)
    (l : FermionicSpace N →L[ℂ] ℂ) (β C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : (coulombPartialOperator N Z).domain,
      β * ‖(x : FermionicSpace N)‖^2 ≤
        (inner ℂ (x : FermionicSpace N) (coulombPartialOperator N Z x)).re +
          C * ‖l (x : FermionicSpace N)‖^2)
    (trial : (coulombPartialOperator N Z).domain)
    (htrial : ‖(trial : FermionicSpace N)‖ = 1)
    (htrialβ : (inner ℂ (trial : FermionicSpace N)
      (coulombPartialOperator N Z trial)).re < β) :
    (variationalGroundEnergy N Z).toReal < β ∧
    ∃ g : (coulombPartialOperator N Z).domain,
      ‖(g : FermionicSpace N)‖ = 1 ∧
      coulombPartialOperator N Z g =
        ((variationalGroundEnergy N Z).toReal : ℂ) • (g : FermionicSpace N) ∧
      (∀ w : (coulombPartialOperator N Z).domain,
        inner ℂ (g : FermionicSpace N) (w : FermionicSpace N) = 0 →
        β * ‖(w : FermionicSpace N)‖^2 ≤
          (inner ℂ (w : FermionicSpace N) (coulombPartialOperator N Z w)).re) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z),
        z = ((variationalGroundEnergy N Z).toReal : ℂ) ∨ β ≤ z.re) := by
  let A := coulombPartialOperator N Z
  let e := (variationalGroundEnergy N Z).toReal
  have hA := coulombPartialOperator_selfAdjoint N Z
  have hsym := TheoremT.OperatorTheory.selfAdjoint_formalAdjoint hA
  have heβ : e < β := (coulomb_ground_energy_le_domain_rayleigh N Z trial htrial).trans_lt htrialβ
  obtain ⟨g,hg,hAg⟩ := TheoremT.OperatorTheory.selfAdjoint_spectral_eigenvector_of_scalar_defect
    A hA l β C hC hbound e (coulomb_variational_energy_mem_spectrum N Z) heβ
  have hcomp := TheoremT.OperatorTheory.rankOne_ground_complement A hsym l C β hbound
    g hg e hAg heβ
  refine ⟨heβ,g,hg,hAg,hcomp,?_⟩
  intro z hz
  by_cases hβ : β ≤ z.re
  · exact Or.inr hβ
  have hzreal := coulomb_spectrum_real N Z hz
  have heq : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hzreal]
  by_cases he : z.re = e
  · left
    rw [← heq,he]
  right
  have hzr : (z.re : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum A := by
    rwa [heq]
  obtain ⟨u,hu,hAu⟩ := TheoremT.OperatorTheory.selfAdjoint_spectral_eigenvector_of_scalar_defect
    A hA l β C hC hbound z.re hzr (lt_of_not_ge hβ)
  have ho := TheoremT.OperatorTheory.symmetric_domain_eigenvectors_orthogonal
    A hsym g u e z.re (Ne.symm he) hAg hAu
  have hb := hcomp u ho
  rw [hu,hAu,inner_smul_right,inner_self_eq_norm_sq_to_K,hu] at hb
  simpa using hb

#print axioms coulomb_ground_energy_le_domain_rayleigh
#print axioms coulomb_rankOne_ground_branch
end TheoremT.Continuum
