import ManyBody.S8.ExactProductGroundPointwise
import PhysicalKSBoxAnalyticDescentData_v1

/-! Physical analytic descent for the exact-product charge separator,
including Z=3/2, using the recovered actual factorial and descent APIs.
The existing actual normalized two-electron fermionic ground state and
all its spectral, weak H2 and singlet statements are retained. Its physical
chart pointwise clauses now include analyticity and the actual physical
A plus distance times B identity, with the original common constants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

set_option maxHeartbeats 1200000 in
theorem exactProduct_physical_ground_analytic_descent (Z : ℝ) (hZ : 0 < Z)
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
            PhysicalKSBoxAnalyticDescentData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,g,hg,hEg,hspec,hmem,hlower,
    F,hF,hFS,hH2,hFgraph,hSinglet,u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,hN,hP⟩ :=
      exactProduct_physical_ground_pointwise Z hZ hα hsep
  refine ⟨C_H,M,A,hCH,hM,hA,g,hg,hEg,hspec,hmem,hlower,
    F,hF,hFS,hH2,hFgraph,hSinglet,u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro ε hε hlim σ i t0 ht0
    exact nuclearKSPhysicalAnalyticDescent_data (originScaledDifference (u σ) ε) i
      (hN ε hε hlim σ i t0 ht0) hA hF0
  · intro ε hε hlim σ t0 ht0
    exact pairKSPhysicalAnalyticDescent_data (originScaledDifference (u σ) ε)
      (hP ε hε hlim σ t0 ht0) hA hF0

#print axioms exactProduct_physical_ground_analytic_descent

theorem exactProduct_physical_ground_analytic_descent_above_threshold (Z : ℝ)
    (hZ : (20+5*Real.sqrt 10)/24 < Z) :
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
            PhysicalKSBoxAnalyticDescentData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  obtain ⟨hZ0,hα,hsep⟩ := ManyBody.S2.exactProduct_charge_conditions Z hZ
  exact exactProduct_physical_ground_analytic_descent Z hZ0 hα hsep

theorem exactProduct_three_halves_physical_analytic_descent :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∃ g : (coulombPartialOperator 2 (3/2 : ℝ)).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 (3/2 : ℝ) g =
        ((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : ℂ) • (g : FermionicSpace 2) ∧
      spectralGroundEnergy 2 (3/2 : ℝ) = ((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : EReal) ∧
      (((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : ℂ) ∈
        TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 (3/2 : ℝ))) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 (3/2 : ℝ)),
        (variationalGroundEnergy 2 (3/2 : ℝ)).toReal ≤ z.re) ∧
      ∃ F : SpatialL2 2, ‖F‖ = 1 ∧ pullback twoElectronSwap F = F ∧ HasH2 F ∧
        scalarHamiltonianGraph 2 (3/2 : ℝ) F
          (((variationalGroundEnergy 2 (3/2 : ℝ)).toReal : ℂ) • F) ∧
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
          coulombMoserBoundCoefficient 2 (3/2 : ℝ) (variationalGroundEnergy 2 (3/2 : ℝ)).toReal *
            ‖(g : FermionicSpace 2).val‖) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  exact exactProduct_physical_ground_analytic_descent (3/2)
    (by norm_num) (by norm_num) (by norm_num)

#print axioms exactProduct_physical_ground_analytic_descent_above_threshold
#print axioms exactProduct_three_halves_physical_analytic_descent
end ManyBody.S8
