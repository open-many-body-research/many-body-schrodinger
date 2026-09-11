import TwoElectronPhysicalGroundBranch_v1
import CoulombRankOneCertificate_v1

/-! A continuum spectral enclosure with the actual physical comparison proved.
The certificate inputs are a unit H² vector and directed mean/residual bounds.
No executable producer, approximation rate, or bit complexity is asserted here. -/
noncomputable section
namespace TheoremT.Continuum

theorem twoElectron_physical_directed_spectral_enclosure (Z : ℝ) (hZ : 0 < Z)
    (ψ : (coulombPartialOperator 2 Z).domain) (hψ : ‖(ψ : FermionicSpace 2)‖ = 1)
    (L U r : ℝ)
    (hL : L ≤ (inner ℂ (ψ : FermionicSpace 2) (coulombPartialOperator 2 Z ψ)).re)
    (hU : (inner ℂ (ψ : FermionicSpace 2) (coulombPartialOperator 2 Z ψ)).re ≤ U)
    (hUβ : U < -(5*Z^2/8))
    (hr : ‖coulombPartialOperator 2 Z ψ -
      ((inner ℂ (ψ : FermionicSpace 2) (coulombPartialOperator 2 Z ψ)).re : ℂ) •
        (ψ : FermionicSpace 2)‖^2 ≤ r) :
    ((L-r/(-(5*Z^2/8)-U) : ℝ) : EReal) ≤ spectralGroundEnergy 2 Z ∧
      spectralGroundEnergy 2 Z ≤ (U : EReal) := by
  apply coulomb_rankOne_directed_spectral_enclosure 2 Z
    (innerSL ℂ (hydrogenicSinglet Z hZ)) (-(5*Z^2/8)) (3*Z^2/8)
    (by positivity) ?_ ψ hψ L U r hL hU hUβ hr
  intro x
  have h := twoElectron_operator_rank_one Z hZ x
  change -(5*Z^2/8) * ‖(x : FermionicSpace 2)‖^2 ≤
    (inner ℂ (x : FermionicSpace 2) (coulombPartialOperator 2 Z x)).re +
      (3*Z^2/8) * ‖inner ℂ (hydrogenicSinglet Z hZ) (x : FermionicSpace 2)‖^2
  linarith

#print axioms twoElectron_physical_directed_spectral_enclosure
end TheoremT.Continuum
