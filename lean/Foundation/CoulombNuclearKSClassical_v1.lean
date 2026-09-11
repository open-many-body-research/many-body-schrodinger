import NuclearKSPrincipalIdentity_v1
import NuclearKSPotential_v1
import CoulombPointwiseEquation_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_nuclear_KS_classical_equation {N : ℕ} (i : Fin N)
    {Z E : ℝ} {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g) (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    (q : NuclearKSSpace i) (hq : q ∈ nuclearKSCoefficientPatch i) (hy : q.1 ≠ 0) :
    ContDiffAt ℝ ∞ (g ∘ nuclearKSLift i) q ∧
      nuclearKSPrincipal i (g ∘ nuclearKSLift i) q =
        nuclearKSPotential i Z E q • (g ∘ nuclearKSLift i) q := by
  have hx := nuclearKSCoefficientPatch_off_zero_collisionFree i hq hy
  have hgs := scalar_coulomb_continuous_rep_smooth_away hgraph hg hfg hx
  refine ⟨hgs.comp q (nuclearKSLift_contDiff i).contDiffAt,?_⟩
  rw [nuclear_KS_principal_identity i q (hgs.of_le (by simp)),
    scalar_coulomb_continuous_rep_pointwise_equation hgraph hg hfg hx,
    nuclearKSPotential_eq_coulomb_scaled i Z E q hy]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_ofNat,Function.comp_apply]
  ring

theorem scalar_coulomb_nuclear_KS_classical_pullback {N : ℕ} (i : Fin N)
    {Z E : ℝ} {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃ g : Configuration N → ℂ, LocallyLipschitz g ∧
      ((f : Configuration N → ℂ) =ᵐ[volume] g) ∧
      LocallyLipschitz (g ∘ nuclearKSLift i) ∧
      ∀ q, q ∈ nuclearKSCoefficientPatch i → q.1 ≠ 0 →
        ContDiffAt ℝ ∞ (g ∘ nuclearKSLift i) q ∧
        nuclearKSPrincipal i (g ∘ nuclearKSLift i) q =
          nuclearKSPotential i Z E q • (g ∘ nuclearKSLift i) q := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨g,hg,hfg⟩ := scalar_coulomb_locally_lipschitz_representative hN hgraph
  exact ⟨g,hg,hfg,hg.comp (nuclearKSLift_locallyLipschitz i),
    fun q hq hy => scalar_coulomb_nuclear_KS_classical_equation i hgraph hg.continuous hfg q hq hy⟩

#print axioms scalar_coulomb_nuclear_KS_classical_equation
#print axioms scalar_coulomb_nuclear_KS_classical_pullback
end TheoremT.Continuum
