import SpinOriginFactorialBudgets_v1

/-! A genuine full-spin Coulomb representative and scale-uniform weighted
factorial bounds in every two-electron KS chart. The coefficient constants
precede the input spin vector. One source/H12 amplitude budget, representative,
Lipschitz constant and positive radius work for every spin and every chart.
The conclusion still concerns actual weak L2 profiles, not KS descent. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace TheoremT.Continuum
open WeakGrushin

theorem coulomb_spin_physical_factorial_representative (Z E : ℝ) :
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
            PhysicalKSBoxFactorialData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxFactorialData
              ((originScaledDifference (u σ) ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              t0 M A (spinOriginFactorialSourceBudget M u)
              (spinOriginH12Budget C_H L u)) := by
  classical
  obtain ⟨C_H,M,A,hCH,hM,hA,hgain⟩ := scalar_coulomb_all_physical_box_factorial Z E
  refine ⟨C_H,M,A,hCH,hM,hA,?_⟩
  intro ψ hgraph
  obtain ⟨u,L,R,hR,hu,hLip,hAE,hperm,hbound,_hNamp,_hPamp⟩ :=
    coulomb_spin_KS_scaled_amplitude_representative hgraph
  have hCH0 : 0 ≤ C_H := zero_le_one.trans hCH
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hF0 : 0 ≤ spinOriginFactorialSourceBudget M u := by
    unfold spinOriginFactorialSourceBudget
    positivity
  have hW : 0 ≤ spinOriginH12Budget C_H L u := by
    unfold spinOriginH12Budget
    positivity
  have hσAE (σ : SpinConfiguration 2) :
      (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hAE] with x hx
    exact hx σ
  have hσgraph (σ : SpinConfiguration 2) :
      scalarHamiltonianGraph 2 Z (ψ σ) ((E : ℂ) • ψ σ) := hgraph.2.2 σ
  refine ⟨u,L,R,hR,hF0,hW,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro ε hε hlim σ i t0 ht0
    exact ((hgain (ψ σ) (hσgraph σ) (u σ) (hu σ).continuous (hσAE σ)
      L R ε (hLip σ) hε hlim).1 i t0 ht0).mono_spin_budget hCH hM hA
  · intro ε hε hlim σ t0 ht0
    exact ((hgain (ψ σ) (hσgraph σ) (u σ) (hu σ).continuous (hσAE σ)
      L R ε (hLip σ) hε hlim).2 t0 ht0).mono_spin_budget hCH hM hA

end TheoremT.Continuum
