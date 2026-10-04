import ManyBody.S8.CoulombSpinPhysicalOriginalNormFactorial
import PhysicalKSBoxAnalyticDescentData_v2

/-! The actual full-spin Coulomb graph supplies analytic-plus-distance data
and genuine complex/real coordinate mixed derivatives with a common amplitude
linear in the original state norm. Constants precede the state, representative,
spin, scale, chart, center and derivative multiindices. The original corrected
dimension factor 24, quarter polydisc and physical Euclidean reconstruction
neighborhood are retained without alteration. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

theorem physicalKSDescentDerivativeBudget_original_norm {N : ℕ} (ψ : SpinSpace N)
    (M A Csrc CH12 : ℝ) (hH12 : 0 ≤ CH12) (α β : Fin 3 → ℕ) :
    physicalKSDescentDerivativeBudget M A (Csrc*‖ψ‖) (CH12*‖ψ‖^2) α β =
      physicalKSDescentDerivativeBudget M A Csrc CH12 α β * ‖ψ‖ := by
  unfold physicalKSDescentDerivativeBudget
  rw [physicalKSPointwiseAmplitude_original_norm ψ M A Csrc CH12 hH12]
  ring

def PhysicalKSBoxOriginalNormAnalyticDerivativeData
    (f : Space (Fin 3) → ℂ) (v : Position → Position → ℂ) (t0 : Position)
    (M A Csrc CH12 : ℝ) (ψ : SpinSpace 2) : Prop :=
  PhysicalKSBoxAnalyticDescentDerivativeData f v t0 M A (Csrc*‖ψ‖) (CH12*‖ψ‖^2) ∧
  (∀ z : Fin 3 ⊕ Fin 3 → ℂ,
    (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4 →
    (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4 →
    ∀ α β : Fin 3 → ℕ,
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentA f t0) (Sum.elim α β) z‖ ≤
      physicalKSDescentDerivativeBudget M A Csrc CH12 α β*‖ψ‖ ∧
    ‖complexMultiindexDeriv (physicalKSAnalyticDescentB f t0) (Sum.elim α β) z‖ ≤
      ((32*(7*physicalKSPointwiseRate M A)^2)*
        physicalKSDescentDerivativeBudget M A Csrc CH12 α β)*‖ψ‖) ∧
  (∀ z : Fin 3 ⊕ Fin 3 → ℝ,
    (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4 →
    (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4 →
    ∀ α β : Fin 3 → ℕ,
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentA f t0 (fun i => (x i : ℂ)))
      (Sum.elim α β) z‖ ≤ physicalKSDescentDerivativeBudget M A Csrc CH12 α β*‖ψ‖ ∧
    ‖realMultiindexDeriv
      (fun x : Fin 3 ⊕ Fin 3 → ℝ => physicalKSAnalyticDescentB f t0 (fun i => (x i : ℂ)))
      (Sum.elim α β) z‖ ≤
      ((32*(7*physicalKSPointwiseRate M A)^2)*
        physicalKSDescentDerivativeBudget M A Csrc CH12 α β)*‖ψ‖)

theorem physicalKSBoxAnalyticDerivativeData_to_original_norm
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {t0 : Position} {M A Csrc CH12 : ℝ} {ψ : SpinSpace 2}
    (hH12 : 0 ≤ CH12)
    (hdata : PhysicalKSBoxAnalyticDescentDerivativeData
      f v t0 M A (Csrc*‖ψ‖) (CH12*‖ψ‖^2)) :
    PhysicalKSBoxOriginalNormAnalyticDerivativeData f v t0 M A Csrc CH12 ψ := by
  refine ⟨hdata,?_,?_⟩
  · intro z hX hs α β
    have hb := hdata.2.1 z hX hs α β
    rw [physicalKSDescentDerivativeBudget_original_norm ψ M A Csrc CH12 hH12 α β] at hb
    simpa only [mul_assoc] using hb
  · intro z hX hs α β
    have hb := hdata.2.2 z hX hs α β
    rw [physicalKSDescentDerivativeBudget_original_norm ψ M A Csrc CH12 hH12 α β] at hb
    simpa only [mul_assoc] using hb

theorem coulomb_spin_physical_original_norm_analytic_derivative (Z E : ℝ) :
    ∃ M A : ℝ, ∃ C_L : ℝ≥0, ∃ Csrc CH12 : ℝ,
      1 ≤ M ∧ 1 ≤ A ∧ 0 ≤ Csrc ∧ 0 ≤ CH12 ∧
      ∀ ψ : SpinSpace 2, hamiltonianGraph 2 Z ψ ((E : ℂ) • ψ) →
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith (C_L * ‖ψ‖₊) (u σ) (ball 0 1)) ∧
        (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z E * ‖ψ‖) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxOriginalNormAnalyticDerivativeData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference (u σ) ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A Csrc CH12 ψ) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxOriginalNormAnalyticDerivativeData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference (u σ) ε (pairKSPhysicalCoordinates X T))
              t0 M A Csrc CH12 ψ) := by
  obtain ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,hgain⟩ :=
    coulomb_spin_physical_original_norm_pointwise Z E
  refine ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,?_⟩
  intro ψ hgraph
  obtain ⟨u,hu,hLip,hAE,hperm,hbound,hN,hP⟩ := hgain ψ hgraph
  have hF0 : 0 ≤ Csrc*‖ψ‖ := mul_nonneg hsrc (norm_nonneg ψ)
  refine ⟨u,hu,hLip,hAE,hperm,hbound,?_,?_⟩
  · intro ε hε hlim σ i t0 ht0
    exact physicalKSBoxAnalyticDerivativeData_to_original_norm hH12
      (nuclearKSPhysicalAnalyticDescent_derivative_data (originScaledDifference (u σ) ε) i
        (hN ε hε hlim σ i t0 ht0) hA hF0)
  · intro ε hε hlim σ t0 ht0
    exact physicalKSBoxAnalyticDerivativeData_to_original_norm hH12
      (pairKSPhysicalAnalyticDescent_derivative_data (originScaledDifference (u σ) ε)
        (hP ε hε hlim σ t0 ht0) hA hF0)

#print axioms physicalKSDescentDerivativeBudget_original_norm
#print axioms physicalKSBoxAnalyticDerivativeData_to_original_norm
#print axioms coulomb_spin_physical_original_norm_analytic_derivative
end ManyBody.S8

