import TwoElectronPhysicalGroundBranch_v1
import HardyRankOneTemple_v1

/-! The actual two-electron ground eigenspace is a complex line.
Normalized vectors are unique up to phase, not literally unique. -/
noncomputable section
namespace TheoremT.Continuum

theorem twoElectron_ground_eigenspace_line (Z : ℝ) (hZ : 0 < Z)
    (hsep : 32 < 9*Z^2) :
    ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      ∀ u : (coulombPartialOperator 2 Z).domain,
        coulombPartialOperator 2 Z u =
          ((variationalGroundEnergy 2 Z).toReal : ℂ) • (u : FermionicSpace 2) →
        (u : FermionicSpace 2) =
          inner ℂ (g : FermionicSpace 2) (u : FermionicSpace 2) • (g : FermionicSpace 2) := by
  obtain ⟨hgap,g,hg,hEg,hcomp,_⟩ := twoElectron_physical_ground_branch Z hZ hsep
  exact ⟨g,hg,hEg,fun u hEu =>
    TheoremT.OperatorTheory.ground_complement_eigenspace_rank_one
      (coulombPartialOperator 2 Z) g hg _ _ hEg hgap hcomp u hEu⟩

theorem twoElectron_normalized_ground_phase (Z : ℝ) (hZ : 0 < Z)
    (hsep : 32 < 9*Z^2) :
    ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      ∀ u : (coulombPartialOperator 2 Z).domain,
        ‖(u : FermionicSpace 2)‖ = 1 →
        coulombPartialOperator 2 Z u =
          ((variationalGroundEnergy 2 Z).toReal : ℂ) • (u : FermionicSpace 2) →
        ∃ c : ℂ, ‖c‖ = 1 ∧ (u : FermionicSpace 2) = c • (g : FermionicSpace 2) := by
  obtain ⟨g,hg,hEg,hline⟩ := twoElectron_ground_eigenspace_line Z hZ hsep
  refine ⟨g,hg,hEg,fun u hu hEu => ?_⟩
  refine ⟨inner ℂ (g : FermionicSpace 2) (u : FermionicSpace 2),?_,hline u hEu⟩
  have h := congrArg norm (hline u hEu)
  simpa only [hu,norm_smul,hg,mul_one] using h.symm

#print axioms twoElectron_ground_eigenspace_line
#print axioms twoElectron_normalized_ground_phase
end TheoremT.Continuum
