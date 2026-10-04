import CoulombSpinPhysicalPointwise_v1
import PhysicalKSBoxAnalyticDescentData_v1

/-! Actual full-spin Coulomb representatives retain their original common
pointwise data and now carry the literal analytic A/B decomposition at every
spin, permitted scale, unit center and physical nuclear/pair chart. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem coulomb_spin_physical_analytic_descent_representative (Z E : ℝ) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∀ ψ : SpinSpace 2, hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ) →
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
      ∃ L : ℝ≥0, ∃ R : ℝ,
        0 < R ∧ 0 ≤ spinOriginFactorialSourceBudget M u ∧
        0 ≤ spinOriginH12Budget C_H L u ∧
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith L (u σ) (ball 0 R)) ∧
        (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
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
              ((originScaledDifference (u σ) ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,hgain⟩ := coulomb_spin_physical_pointwise_representative Z E
  refine ⟨C_H,M,A,hCH,hM,hA,?_⟩
  intro ψ hgraph
  obtain ⟨u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,hN,hP⟩ := hgain ψ hgraph
  refine ⟨u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro ε hε hlim σ i t0 ht0
    exact nuclearKSPhysicalAnalyticDescent_data (originScaledDifference (u σ) ε) i
      (hN ε hε hlim σ i t0 ht0) hA hF0
  · intro ε hε hlim σ t0 ht0
    exact pairKSPhysicalAnalyticDescent_data (originScaledDifference (u σ) ε)
      (hP ε hε hlim σ t0 ht0) hA hF0

end TheoremT.Continuum
