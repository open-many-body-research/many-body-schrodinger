import PairKSPrincipalIdentity_v1
import PairKSPotential_v1
import CoulombPointwiseEquation_v1

/-! Classical pair-KS equation for the actual continuous representative of an
N=2 weak H2 Coulomb eigenfunction, off the selected pair collision. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_pair_KS_classical_equation
    {Z E : ℝ} {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    {g : Configuration 2 → ℂ} (hg : Continuous g) (hfg : (f : Configuration 2 → ℂ) =ᵐ[volume] g)
    (q : PairKSSpace) (hq : q ∈ pairKSCoefficientPatch) (hy : q.1 ≠ 0) :
    ContDiffAt ℝ ∞ (g ∘ pairKSLift) q ∧
      ksScaledPrincipal (0 : Fin 2) 1 (g ∘ pairKSLift) q =
        pairKSPotential Z E q • (g ∘ pairKSLift) q := by
  have hx := pairKSCoefficientPatch_off_zero_collisionFree hq hy
  have hgs := scalar_coulomb_continuous_rep_smooth_away hgraph hg hfg hx
  refine ⟨hgs.comp q pairKSLift_contDiff.contDiffAt,?_⟩
  rw [pair_KS_principal_identity q (hgs.of_le (by simp)),
    scalar_coulomb_continuous_rep_pointwise_equation hgraph hg hfg hx,
    pairKSPotential_eq_coulomb_scaled Z E q hy]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_ofNat,Function.comp_apply]
  ring

theorem scalar_coulomb_pair_KS_classical_pullback
    {Z E : ℝ} {f : SpatialL2 2} (hgraph : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f)) :
    ∃ g : Configuration 2 → ℂ, LocallyLipschitz g ∧
      ((f : Configuration 2 → ℂ) =ᵐ[volume] g) ∧
      LocallyLipschitz (g ∘ pairKSLift) ∧
      ∀ q, q ∈ pairKSCoefficientPatch → q.1 ≠ 0 →
        ContDiffAt ℝ ∞ (g ∘ pairKSLift) q ∧
        ksScaledPrincipal (0 : Fin 2) 1 (g ∘ pairKSLift) q =
          pairKSPotential Z E q • (g ∘ pairKSLift) q := by
  obtain ⟨g,hg,hfg⟩ := scalar_coulomb_locally_lipschitz_representative (by decide : 0 < 2) hgraph
  exact ⟨g,hg,hfg,hg.comp pairKSLift_locallyLipschitz,
    fun q hq hy => scalar_coulomb_pair_KS_classical_equation hgraph hg.continuous hfg q hq hy⟩

#print axioms scalar_coulomb_pair_KS_classical_equation
#print axioms scalar_coulomb_pair_KS_classical_pullback
end TheoremT.Continuum
