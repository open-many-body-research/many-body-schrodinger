import TwoElectronPhysicalRankOne_v1
import CoulombRankOneBranch_v1
import CoulombH1GraphEnergy_v1

/-! The actual full H2 fermionic Coulomb operator satisfies the hydrogenic
rank-one comparison. Only a strict physical trial remains to instantiate the
previous ground-attainment and spectral-separation machinery. -/
noncomputable section
namespace TheoremT.Continuum
open TheoremT.Polar

def hydrogenicSinglet (Z : ℝ) (hZ : 0 < Z) : FermionicSpace 2 :=
  twoElectronFermionicSinglet (normalizedPolarGround configuration_one_finrank Z hZ)

theorem hydrogenicSinglet_norm (Z : ℝ) (hZ : 0 < Z) : ‖hydrogenicSinglet Z hZ‖ = 1 :=
  twoElectronFermionicSinglet_norm _ (normalizedPolarGround_norm configuration_one_finrank Z hZ)

theorem twoElectron_operator_rank_one (Z : ℝ) (hZ : 0 < Z)
    (x : (coulombPartialOperator 2 Z).domain) :
    -(5*Z^2/8) * ‖(x : FermionicSpace 2)‖^2 ≤
      (inner ℂ (x : FermionicSpace 2) (coulombPartialOperator 2 Z x)).re +
      (3*Z^2/8) * ‖inner ℂ (hydrogenicSinglet Z hZ) (x : FermionicSpace 2)‖^2 := by
  have h := twoElectron_h1_form_rank_one Z hZ x.val _
    (hamiltonian_graph_formValue (coulombPartialOperator_apply_graph 2 Z x))
  rw [rayleighNumerator_eq_re_complex_inner] at h
  exact h

theorem twoElectron_ground_branch_of_strict_trial (Z : ℝ) (hZ : 0 < Z)
    (trial : (coulombPartialOperator 2 Z).domain)
    (hn : ‖(trial : FermionicSpace 2)‖ = 1)
    (he : (inner ℂ (trial : FermionicSpace 2) (coulombPartialOperator 2 Z trial)).re <
      -(5*Z^2/8)) :
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
  exact coulomb_rankOne_ground_branch 2 Z (innerSL ℂ (hydrogenicSinglet Z hZ))
    (-(5*Z^2/8)) (3*Z^2/8) (by positivity) (twoElectron_operator_rank_one Z hZ)
    trial hn he

#print axioms hydrogenicSinglet_norm
#print axioms twoElectron_operator_rank_one
#print axioms twoElectron_ground_branch_of_strict_trial
end TheoremT.Continuum
