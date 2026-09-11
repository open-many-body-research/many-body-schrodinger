import CoulombNuclearKSOffZeroWeak_v1
import GrushinLocalCoefficientRemovability_v1

/-! The physical nuclear KS weak equation across y=0, on its exact coefficient
patch. The pullback uses the actual continuous representative of an H2 Coulomb
eigenfunction, and all spectator coordinates are retained. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_nuclear_KS_weak {N : ℕ} (i : Fin N)
    {Z E : ℝ} {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g) (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ nuclearKSCoefficientPatch i) :
    Integrable (fun q => (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
      (g ∘ nuclearKSLift i) q) volume ∧
    (∫ q, (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
      (g ∘ nuclearKSLift i) q)=0 := by
  have hw : ∀ ψ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ nuclearKSCoefficientPatch i \ {q | q.1=0} →
      (∫ q, (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) ψ q : ℂ)*
        (g ∘ nuclearKSLift i) q) = ∫ q, (ψ q : ℂ)*(0:ℂ) := by
    intro ψ hψ hcψ hsψ
    simpa only [mul_zero,integral_zero] using
      (scalar_coulomb_nuclear_KS_off_zero_weak i hgraph hg hfg hψ hcψ hsψ).2
  have hh := nuclear_KS_local_coefficient_Grushin_removability i 4 spectatorBasis
    (nuclearKSCoefficientPatch_isOpen i) (fun q hq => nuclearKSPotential_contDiffAt i Z E hq)
    (hg.comp (nuclearKSLift_contDiff i).continuous) (f := fun _ => (0:ℂ)) continuous_const
    hw hφ hc hs
  exact ⟨hh.1,by simpa only [mul_zero,integral_zero] using hh.2.2⟩

theorem scalar_coulomb_nuclear_KS_weak_pullback {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃ g : Configuration N → ℂ, LocallyLipschitz g ∧
      ((f : Configuration N → ℂ) =ᵐ[volume] g) ∧
      ∀ i : Fin N, LocallyLipschitz (g ∘ nuclearKSLift i) ∧
        ∀ φ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ nuclearKSCoefficientPatch i →
          Integrable (fun q => (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
            (g ∘ nuclearKSLift i) q) volume ∧
          (∫ q, (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
            (g ∘ nuclearKSLift i) q)=0 := by
  obtain ⟨g,hg,hfg⟩ := scalar_coulomb_locally_lipschitz_representative hN hgraph
  refine ⟨g,hg,hfg,?_⟩
  intro i
  exact ⟨hg.comp (nuclearKSLift_locallyLipschitz i),
    fun φ hφ hc hs => scalar_coulomb_nuclear_KS_weak i hgraph hg.continuous hfg hφ hc hs⟩

#print axioms scalar_coulomb_nuclear_KS_weak
#print axioms scalar_coulomb_nuclear_KS_weak_pullback
end TheoremT.Continuum
