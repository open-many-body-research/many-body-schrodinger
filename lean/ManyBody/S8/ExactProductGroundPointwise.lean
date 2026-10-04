import CoulombSpinPhysicalPointwise_v1
import ManyBody.S2.HydrogenProductRepulsionExact
import TwoElectronGroundSpatial_v1
import CoulombSpectralFoundation_v3

/-! Exact optimized-repulsion ground branch, extending the recovered physical
pointwise factorial endpoint to the new strict charge separator.
Actual normalized two-electron fermionic ground state, identified with
the bottom of the continuum spectrum, and shared full-spin pointwise KS factorial
bounds. No eigenfunction, representative or analytic estimate is assumed.
The exact weak H2 operator domain and spatial singlet link remain explicit. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

set_option maxHeartbeats 1200000 in
theorem exactProduct_physical_ground_pointwise (Z : ℝ) (hZ : 0 < Z)
    (hα : 0 < Z-5/16) (hsep : 5*Z^2/8 < (Z-5/16)^2) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      spectralGroundEnergy 2 Z = ((variationalGroundEnergy 2 Z).toReal : EReal) ∧
      (((variationalGroundEnergy 2 Z).toReal : ℂ) ∈
        TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
        (variationalGroundEnergy 2 Z).toReal ≤ z.re) ∧
      ∃ F : SpatialL2 2, ‖F‖ = 1 ∧ pullback twoElectronSwap F = F ∧ HasH2 F ∧
        scalarHamiltonianGraph 2 Z F
          (((variationalGroundEnergy 2 Z).toReal : ℂ) • F) ∧
        (g : FermionicSpace 2).val = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • spinSingletLift F ∧
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
      ∃ L : ℝ≥0, ∃ R : ℝ,
        0 < R ∧ 0 ≤ spinOriginFactorialSourceBudget M u ∧
        0 ≤ spinOriginH12Budget C_H L u ∧
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith L (u σ) (ball 0 R)) ∧
        (∀ᵐ x ∂volume, ∀ σ, (g : FermionicSpace 2).val σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal *
            ‖(g : FermionicSpace 2).val‖) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxPointwiseData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxPointwiseData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,hgain⟩ := coulomb_spin_physical_pointwise_representative Z
    (variationalGroundEnergy 2 Z).toReal
  obtain ⟨_htrial,hE,g,hg,hEg,_hline,_hcomp,_hrest⟩ :=
    ManyBody.S2.exactProduct_ground_branch Z hZ hα hsep
  obtain ⟨F,hF,hFS,hH2,hFgraph,hSinglet⟩ :=
    twoElectron_low_eigen_spatial_amplitude Z hZ g hg _ hE hEg
  have hgraph : hamiltonianGraph 2 Z (g : FermionicSpace 2).val
      (((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2).val) := by
    have hh := coulombPartialOperator_apply_graph 2 Z g
    rw [hEg] at hh
    exact hh
  have hfinite := variational_ground_energy_finite 2 Z
  have hspec : spectralGroundEnergy 2 Z =
      ((variationalGroundEnergy 2 Z).toReal : EReal) := by
    rw [spectralGroundEnergy_eq_variationalGroundEnergy]
    exact (EReal.coe_toReal hfinite.1 hfinite.2).symm
  exact ⟨C_H,M,A,hCH,hM,hA,g,hg,hEg,hspec,coulomb_variational_energy_mem_spectrum 2 Z,
    fun z hz => coulomb_spectrum_re_lower_bound 2 Z hz,
    F,hF,hFS,hH2,hFgraph,hSinglet,hgain (g : FermionicSpace 2).val hgraph⟩

#print axioms exactProduct_physical_ground_pointwise
end ManyBody.S8
