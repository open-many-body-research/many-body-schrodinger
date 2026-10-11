import TwoElectronGroundPhysicalPointwise_v1
import PhysicalKSBoxAnalyticDescentData_v2

/-! The same actual normalized two-electron ground state retains every
spectral, weak H2, singlet and representative conclusion. Each physical
nuclear/pair clause adds complex and real mixed derivatives of the same
literal A/B decomposition, with no new physical hypotheses. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

set_option maxHeartbeats 1200000 in
theorem twoElectron_physical_ground_analytic_descent_derivative (Z : ℝ) (hZ : 0 < Z)
    (hsep : 32 < 9*Z^2) :
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
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference (u σ) ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,g,hg,hEg,hspec,hmem,hlower,
    F,hF,hFS,hH2,hFgraph,hSinglet,u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,hN,hP⟩ :=
      twoElectron_physical_ground_pointwise Z hZ hsep
  refine ⟨C_H,M,A,hCH,hM,hA,g,hg,hEg,hspec,hmem,hlower,
    F,hF,hFS,hH2,hFgraph,hSinglet,u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro ε hε hlim σ i t0 ht0
    exact nuclearKSPhysicalAnalyticDescent_derivative_data (originScaledDifference (u σ) ε) i
      (hN ε hε hlim σ i t0 ht0) hA hF0
  · intro ε hε hlim σ t0 ht0
    exact pairKSPhysicalAnalyticDescent_derivative_data (originScaledDifference (u σ) ε)
      (hP ε hε hlim σ t0 ht0) hA hF0

end TheoremT.Continuum
