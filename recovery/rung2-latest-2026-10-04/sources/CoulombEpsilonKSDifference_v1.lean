import CoulombEpsilonKSWeak_v1
import KSScaledAffineWeakForcing_v1
import LocallyLipschitzScaledDifference_v1

/-! The exact normalized origin difference of an actual Coulomb representative
satisfies the inhomogeneous KS equation, with no inverse epsilon in its source.
Both test integrabilities follow from proved weak identities. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_epsilon_nuclear_KS_difference_weak {N : ℕ} (i : Fin N)
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ nuclearKSCoefficientPatch i) :
    Integrable (fun q =>
      (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*
        originScaledDifference g ε (nuclearKSLift i q)) volume ∧
    Integrable (fun q => φ q • (-(nuclearKSPotential i Z (ε*E) q • g 0))) volume ∧
    (∫ q, (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*
      originScaledDifference g ε (nuclearKSLift i q)) =
        ∫ q, φ q • (-(nuclearKSPotential i Z (ε*E) q • g 0)) := by
  obtain ⟨hi,hw⟩ := scalar_coulomb_epsilon_nuclear_KS_weak i hε hgraph hg hfg hφ hc hs
  have h := ks_scaled_affine_weak_forcing i 4 ε (g 0) hε.ne' hφ hc
    (fun q hq => nuclearKSPotential_contDiffAt i Z (ε*E) (hs hq)) hi hw
  exact h

theorem scalar_coulomb_epsilon_pair_KS_difference_weak
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    {φ : PairKSSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ pairKSCoefficientPatch) :
    Integrable (fun q =>
      (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*
        originScaledDifference g ε (pairKSLift q)) volume ∧
    Integrable (fun q => φ q • (-(pairKSPotential Z (ε*E) q • g 0))) volume ∧
    (∫ q, (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*
      originScaledDifference g ε (pairKSLift q)) =
        ∫ q, φ q • (-(pairKSPotential Z (ε*E) q • g 0)) := by
  obtain ⟨hi,hw⟩ := scalar_coulomb_epsilon_pair_KS_weak hε hgraph hg hfg hφ hc hs
  have h := ks_scaled_affine_weak_forcing (0 : Fin 2) 1 ε (g 0) hε.ne' hφ hc
    (fun q hq => pairKSPotential_contDiffAt Z (ε*E) (hs hq)) hi hw
  exact h

#print axioms scalar_coulomb_epsilon_nuclear_KS_difference_weak
#print axioms scalar_coulomb_epsilon_pair_KS_difference_weak
end TheoremT.Continuum
