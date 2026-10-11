import CoulombEpsilonKSClassical_v1
import KSScaledLocalWeakKernel_v1
import GrushinLocalCoefficientRemovability_v1

/-! Actual physically scaled Coulomb KS equations on the fixed coefficient
patches, including compact tests across the selected collision fiber. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_epsilon_nuclear_KS_off_zero_weak {N : ℕ} (i : Fin N)
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (nuclearKSCoefficientPatch i) \ {q | q.1=0}) :
    Integrable (fun q => (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*g (ε • (nuclearKSLift i) q)) volume ∧
      (∫ q, (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*g (ε • (nuclearKSLift i) q))=0 := by
  have hh (q : NuclearKSSpace i) (hq : q ∈ tsupport φ) :=
    scalar_coulomb_epsilon_nuclear_KS_classical_equation i hε hgraph hg hfg q (hs hq).1 (hs hq).2
  exact ks_scaled_local_classical_kernel_weak i 4 hφ hc
    (fun q hq => (hh q hq).1) (fun q hq => epsilonNuclearKSPotential_contDiffAt i ε Z E (hs hq).1)
    (fun q hq => (hh q hq).2)

theorem scalar_coulomb_epsilon_nuclear_KS_weak {N : ℕ} (i : Fin N)
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ nuclearKSCoefficientPatch i) :
    Integrable (fun q => (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*g (ε • (nuclearKSLift i) q)) volume ∧
      (∫ q, (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) φ q : ℂ)*g (ε • (nuclearKSLift i) q))=0 := by
  have hgε : Continuous (fun x : Configuration N => g (ε • x)) :=
    hg.comp (ε • ContinuousLinearMap.id ℝ (Configuration N)).continuous
  have hw : ∀ ψ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (nuclearKSCoefficientPatch i) \ {q | q.1=0} →
      (∫ q, (splitGrushin 4 spectatorBasis (epsilonNuclearKSPotential i ε Z E) ψ q : ℂ)*
        g (ε • (nuclearKSLift i) q)) = ∫ q, (ψ q : ℂ)*(0:ℂ) := by
    intro ψ hψ hcψ hsψ
    simpa only [mul_zero,integral_zero] using
      (scalar_coulomb_epsilon_nuclear_KS_off_zero_weak i hε hgraph hg hfg hψ hcψ hsψ).2
  have hh := nuclear_KS_local_coefficient_Grushin_removability i 4 spectatorBasis
    (nuclearKSCoefficientPatch_isOpen i) (fun q hq => epsilonNuclearKSPotential_contDiffAt i ε Z E hq)
    (hgε.comp (nuclearKSLift_contDiff i).continuous) (f := fun _ => (0:ℂ)) continuous_const
    hw hφ hc hs
  exact ⟨hh.1,by simpa only [mul_zero,integral_zero,Function.comp_apply] using hh.2.2⟩

theorem scalar_coulomb_epsilon_pair_KS_off_zero_weak 
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    {φ : PairKSSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (pairKSCoefficientPatch) \ {q | q.1=0}) :
    Integrable (fun q => (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*g (ε • (pairKSLift) q)) volume ∧
      (∫ q, (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*g (ε • (pairKSLift) q))=0 := by
  have hh (q : PairKSSpace) (hq : q ∈ tsupport φ) :=
    scalar_coulomb_epsilon_pair_KS_classical_equation hε hgraph hg hfg q (hs hq).1 (hs hq).2
  exact ks_scaled_local_classical_kernel_weak (0 : Fin 2) 1 hφ hc
    (fun q hq => (hh q hq).1) (fun q hq => epsilonPairKSPotential_contDiffAt ε Z E (hs hq).1)
    (fun q hq => (hh q hq).2)

theorem scalar_coulomb_epsilon_pair_KS_weak 
    {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    {φ : PairKSSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ pairKSCoefficientPatch) :
    Integrable (fun q => (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*g (ε • (pairKSLift) q)) volume ∧
      (∫ q, (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) φ q : ℂ)*g (ε • (pairKSLift) q))=0 := by
  have hgε : Continuous (fun x : Configuration 2 => g (ε • x)) :=
    hg.comp (ε • ContinuousLinearMap.id ℝ (Configuration 2)).continuous
  have hw : ∀ ψ : PairKSSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (pairKSCoefficientPatch) \ {q | q.1=0} →
      (∫ q, (splitGrushin 1 spectatorBasis (epsilonPairKSPotential ε Z E) ψ q : ℂ)*
        g (ε • (pairKSLift) q)) = ∫ q, (ψ q : ℂ)*(0:ℂ) := by
    intro ψ hψ hcψ hsψ
    simpa only [mul_zero,integral_zero] using
      (scalar_coulomb_epsilon_pair_KS_off_zero_weak hε hgraph hg hfg hψ hcψ hsψ).2
  have hh := nuclear_KS_local_coefficient_Grushin_removability (0 : Fin 2) 1 spectatorBasis
    pairKSCoefficientPatch_isOpen (fun q hq => epsilonPairKSPotential_contDiffAt ε Z E hq)
    (hgε.comp pairKSLift_contDiff.continuous) (f := fun _ => (0:ℂ)) continuous_const
    hw hφ hc hs
  exact ⟨hh.1,by simpa only [mul_zero,integral_zero,Function.comp_apply] using hh.2.2⟩

#print axioms scalar_coulomb_epsilon_nuclear_KS_off_zero_weak
#print axioms scalar_coulomb_epsilon_nuclear_KS_weak
#print axioms scalar_coulomb_epsilon_pair_KS_off_zero_weak
#print axioms scalar_coulomb_epsilon_pair_KS_weak
end TheoremT.Continuum
