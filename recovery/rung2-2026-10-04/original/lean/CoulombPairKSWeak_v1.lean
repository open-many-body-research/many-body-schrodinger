import CoulombPairKSClassical_v1
import PairKSPotentialSmooth_v1
import KSScaledLocalWeakKernel_v1
import GrushinLocalCoefficientRemovability_v1

/-! The actual N=2 pair KS weak equation, including tests crossing y=0.
The coefficient patch excludes nuclear zeros only. Integrability is proved
along with the equation; no weak-derivative or off-zero equation premise is
assumed for the pullback. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_pair_KS_off_zero_weak
    {Z E : ℝ} {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g) (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    {φ : PairKSSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ pairKSCoefficientPatch \ {q | q.1=0}) :
    Integrable (fun q => (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q) volume ∧
    (∫ q, (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q)=0 := by
  have hh (q : PairKSSpace) (hq : q ∈ tsupport φ) :=
    scalar_coulomb_pair_KS_classical_equation hgraph hg hfg q (hs hq).1 (hs hq).2
  exact ks_scaled_local_classical_kernel_weak (0 : Fin 2) 1 hφ hc
    (fun q hq => (hh q hq).1) (fun q hq => pairKSPotential_contDiffAt Z E (hs hq).1)
    (fun q hq => (hh q hq).2)

theorem scalar_coulomb_pair_KS_weak
    {Z E : ℝ} {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g) (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    {φ : PairKSSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ pairKSCoefficientPatch) :
    Integrable (fun q => (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q) volume ∧
    (∫ q, (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
      (g ∘ pairKSLift) q)=0 := by
  have hw : ∀ ψ : PairKSSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ pairKSCoefficientPatch \ {q | q.1=0} →
      (∫ q, (splitGrushin 1 spectatorBasis (pairKSPotential Z E) ψ q : ℂ)*
        (g ∘ pairKSLift) q) = ∫ q, (ψ q : ℂ)*(0:ℂ) := by
    intro ψ hψ hcψ hsψ
    simpa only [mul_zero,integral_zero] using
      (scalar_coulomb_pair_KS_off_zero_weak hgraph hg hfg hψ hcψ hsψ).2
  have hh := nuclear_KS_local_coefficient_Grushin_removability (0 : Fin 2) 1 spectatorBasis
    pairKSCoefficientPatch_isOpen (fun q hq => pairKSPotential_contDiffAt Z E hq)
    (hg.comp pairKSLift_contDiff.continuous) (f := fun _ => (0:ℂ)) continuous_const
    hw hφ hc hs
  exact ⟨hh.1,by simpa only [mul_zero,integral_zero] using hh.2.2⟩

theorem scalar_coulomb_pair_KS_weak_pullback
    {Z E : ℝ} {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f)) :
    ∃ g : Configuration 2 → ℂ, LocallyLipschitz g ∧
      ((f : Configuration 2 → ℂ) =ᵐ[volume] g) ∧
      LocallyLipschitz (g ∘ pairKSLift) ∧
      ∀ φ : PairKSSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ pairKSCoefficientPatch →
        Integrable (fun q => (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
          (g ∘ pairKSLift) q) volume ∧
        (∫ q, (splitGrushin 1 spectatorBasis (pairKSPotential Z E) φ q : ℂ)*
          (g ∘ pairKSLift) q)=0 := by
  obtain ⟨g,hg,hfg⟩ := scalar_coulomb_locally_lipschitz_representative (by decide : 0 < 2) hgraph
  exact ⟨g,hg,hfg,hg.comp pairKSLift_locallyLipschitz,
    fun φ hφ hc hs => scalar_coulomb_pair_KS_weak hgraph hg.continuous hfg hφ hc hs⟩

#print axioms scalar_coulomb_pair_KS_off_zero_weak
#print axioms scalar_coulomb_pair_KS_weak
#print axioms scalar_coulomb_pair_KS_weak_pullback
end TheoremT.Continuum
