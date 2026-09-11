import HydrogenProductTrialEnergy_v1
import TwoElectronOperatorComparison_v1

/-! The actual fermionic two-electron Coulomb ground branch, with an explicit
charge range that includes helium. Every comparison and strict trial premise
is discharged. Full Theorem T's approximation and algorithm claims are separate. -/
noncomputable section
namespace TheoremT.Continuum

theorem twoElectron_physical_ground_branch (Z : ℝ) (hZ : 0 < Z) (hsep : 32 < 9*Z^2) :
    (variationalGroundEnergy 2 Z).toReal < -(5*Z^2/8) ∧
    ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      (∀ w : (coulombPartialOperator 2 Z).domain,
        inner ℂ (g : FermionicSpace 2) (w : FermionicSpace 2) = 0 →
        -(5*Z^2/8) * ‖(w : FermionicSpace 2)‖^2 ≤
          (inner ℂ (w : FermionicSpace 2) (coulombPartialOperator 2 Z w)).re) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
        z = ((variationalGroundEnergy 2 Z).toReal : ℂ) ∨ -(5*Z^2/8) ≤ z.re) := by
  exact twoElectron_ground_branch_of_strict_trial Z hZ (hydrogenProductTrial Z Z hZ)
    (hydrogenProductTrial_norm Z Z hZ) (hydrogenProductTrial_strict Z hZ hsep)

theorem helium_physical_ground_branch :
    (variationalGroundEnergy 2 2).toReal < -(5/2 : ℝ) ∧
    ∃ g : (coulombPartialOperator 2 2).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 2 g =
        ((variationalGroundEnergy 2 2).toReal : ℂ) • (g : FermionicSpace 2) ∧
      (∀ w : (coulombPartialOperator 2 2).domain,
        inner ℂ (g : FermionicSpace 2) (w : FermionicSpace 2) = 0 →
        -(5/2 : ℝ) * ‖(w : FermionicSpace 2)‖^2 ≤
          (inner ℂ (w : FermionicSpace 2) (coulombPartialOperator 2 2 w)).re) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 2),
        z = ((variationalGroundEnergy 2 2).toReal : ℂ) ∨ -(5/2 : ℝ) ≤ z.re) := by
  convert twoElectron_physical_ground_branch 2 (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms twoElectron_physical_ground_branch
#print axioms helium_physical_ground_branch
end TheoremT.Continuum
