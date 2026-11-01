import CoulombSpinPhysicalFactorial_v1
import CoulombKSPhysicalPointwise_v1

/-! Actual full-spin two-electron Coulomb representatives have analytic KS
pullbacks with explicit common pointwise factorial bounds. All source and
H12 inputs are derived from the actual operator graph, and the same bounds
work for every spin, scale, unit center and nuclear/pair chart. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem coulomb_spin_physical_pointwise_representative (Z E : ℝ) :
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
            PhysicalKSBoxPointwiseData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxPointwiseData
              ((originScaledDifference (u σ) ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,hgain⟩ := coulomb_spin_physical_factorial_representative Z E
  refine ⟨C_H,M,A,hCH,hM,hA,?_⟩
  intro ψ hgraph
  obtain ⟨u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,hN,hP⟩ := hgain ψ hgraph
  refine ⟨u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro ε hε hlim σ i t0 ht0
    have hc : Continuous
        ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) :=
      ((originScaledDifference_continuous (hu σ).continuous ε).comp
        (nuclearKSLift_contDiff i).continuous).comp (physicalSpectatorReindexAt i).symm.continuous
    exact physicalKSBoxFactorialData_to_pointwise (hN ε hε hlim σ i t0 ht0)
      hc.continuousOn hA hF0
  · intro ε hε hlim σ t0 ht0
    have hc : Continuous
        ((originScaledDifference (u σ) ε ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) :=
      ((originScaledDifference_continuous (hu σ).continuous ε).comp
        pairKSLift_contDiff.continuous).comp (physicalSpectatorReindexAt (0 : Fin 2)).symm.continuous
    exact physicalKSBoxFactorialData_to_pointwise (hP ε hε hlim σ t0 ht0)
      hc.continuousOn hA hF0

end TheoremT.Continuum
