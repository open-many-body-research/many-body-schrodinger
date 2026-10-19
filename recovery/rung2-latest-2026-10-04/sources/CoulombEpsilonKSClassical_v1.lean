import CoulombOriginScaling_v1
import EpsilonNuclearKSPotential_v1
import EpsilonPairKSPotential_v1
import NuclearKSPrincipalIdentity_v1
import PairKSPrincipalIdentity_v1

/-! Classical KS equations for the actual physically dilated representative.
The nuclear chart has spectator coefficient 4 and the unscaled pair-center
chart has coefficient 1. Both use the entire epsilon-scaled Coulomb potential. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_epsilon_nuclear_KS_classical_equation {N : ℕ} (i : Fin N)
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    (q : NuclearKSSpace i) (hq : q ∈ nuclearKSCoefficientPatch i) (hy : q.1 ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => g (ε • x)) ∘ nuclearKSLift i) q ∧
      ksScaledPrincipal i 4 ((fun x => g (ε • x)) ∘ nuclearKSLift i) q =
        epsilonNuclearKSPotential i ε Z E q •
          (((fun x => g (ε • x)) ∘ nuclearKSLift i) q) := by
  have hx := nuclearKSCoefficientPatch_off_zero_collisionFree i hq hy
  obtain ⟨hgs,hP⟩ := scalar_coulomb_origin_scaled_classical_equation hε hgraph hg hfg hx
  refine ⟨hgs.comp q (nuclearKSLift_contDiff i).contDiffAt,?_⟩
  rw [ksScaledPrincipal_four,nuclear_KS_principal_identity i q (hgs.of_le (by simp)),
    hP,epsilonNuclearKSPotential_eq_coulomb_scaled i ε Z E q hy]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_ofNat,Function.comp_apply]
  ring

theorem scalar_coulomb_epsilon_pair_KS_classical_equation
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    (q : PairKSSpace) (hq : q ∈ pairKSCoefficientPatch) (hy : q.1 ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => g (ε • x)) ∘ pairKSLift) q ∧
      ksScaledPrincipal (0 : Fin 2) 1 ((fun x => g (ε • x)) ∘ pairKSLift) q =
        epsilonPairKSPotential ε Z E q •
          (((fun x => g (ε • x)) ∘ pairKSLift) q) := by
  have hx := pairKSCoefficientPatch_off_zero_collisionFree hq hy
  obtain ⟨hgs,hP⟩ := scalar_coulomb_origin_scaled_classical_equation hε hgraph hg hfg hx
  refine ⟨hgs.comp q pairKSLift_contDiff.contDiffAt,?_⟩
  rw [pair_KS_principal_identity q (hgs.of_le (by simp)),
    hP,epsilonPairKSPotential_eq_coulomb_scaled ε Z E q hy]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_ofNat,Function.comp_apply]
  ring

#print axioms scalar_coulomb_epsilon_nuclear_KS_classical_equation
#print axioms scalar_coulomb_epsilon_pair_KS_classical_equation
end TheoremT.Continuum
