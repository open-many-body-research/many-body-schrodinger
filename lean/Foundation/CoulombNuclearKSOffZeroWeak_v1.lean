import NuclearKSLocalWeakKernel_v1
import CoulombNuclearKSClassical_v1
import NuclearKSPotentialSmooth_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_nuclear_KS_off_zero_weak {N : ℕ} (i : Fin N)
    {Z E : ℝ} {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g) (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ nuclearKSCoefficientPatch i \ {q | q.1=0}) :
    Integrable (fun q => (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
      (g ∘ nuclearKSLift i) q) volume ∧
    (∫ q, (splitGrushin 4 spectatorBasis (nuclearKSPotential i Z E) φ q : ℂ)*
      (g ∘ nuclearKSLift i) q)=0 := by
  have hh (q : NuclearKSSpace i) (hq : q ∈ tsupport φ) :=
    scalar_coulomb_nuclear_KS_classical_equation i hgraph hg hfg q (hs hq).1 (hs hq).2
  exact nuclear_KS_local_classical_kernel_weak i hφ hc (fun q hq => (hh q hq).1)
    (fun q hq => nuclearKSPotential_contDiffAt i Z E (hs hq).1) (fun q hq => (hh q hq).2)

#print axioms scalar_coulomb_nuclear_KS_off_zero_weak
end TheoremT.Continuum
