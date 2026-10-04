import ManyBody.S8.PhysicalEigenstateLipschitzNormBound
import ManyBody.S8.Internal.PhysicalSpinOriginNormBudgets
import SpinOriginFactorialBudgets_v1
import CoulombKSPhysicalPointwise_v1

/-! The actual full-spin physical Coulomb graph supplies all-order factorial
    and pointwise KS data with source amplitude linear and H12 budget quadratic
    in the original state norm. One fixed physical radius R=1 and one set of
    constants work for all states, spins, scales and unit spectator centers.
    The common constants are existential, not an effective numerical recipe. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin


/-- The all-order weighted-profile amplitude is linear in the original state
    norm under the derived linear/quadratic physical input budgets. -/
theorem physicalKSFactorialAmplitude_original_norm {N : ℕ} (ψ : SpinSpace N)
    (M A Csrc CH12 : ℝ) (hH12 : 0 ≤ CH12) (r : ℕ) :
    12 * commonKSBoxFactorialConstant M * A *
      (Csrc * ‖ψ‖ + 498 * Real.sqrt (CH12 * ‖ψ‖^2)) *
      (3072 * commonKSBoxFactorialConstant M * A)^r * (r.factorial : ℝ) =
    (12 * commonKSBoxFactorialConstant M * A * (Csrc + 498 * Real.sqrt CH12) *
      (3072 * commonKSBoxFactorialConstant M * A)^r * (r.factorial : ℝ)) * ‖ψ‖ := by
  rw [Real.sqrt_mul hH12, Real.sqrt_sq (norm_nonneg ψ)]
  ring
/-- The recovered pointwise amplitude is exactly linear in the original norm
    when its source budget is linear and its H12 budget is quadratic. -/
theorem physicalKSPointwiseAmplitude_original_norm {N : ℕ} (ψ : SpinSpace N)
    (M A Csrc CH12 : ℝ) (hH12 : 0 ≤ CH12) :
    physicalKSPointwiseAmplitude M A (Csrc * ‖ψ‖) (CH12 * ‖ψ‖^2) =
      physicalKSPointwiseAmplitude M A Csrc CH12 * ‖ψ‖ := by
  unfold physicalKSPointwiseAmplitude
  rw [Real.sqrt_mul hH12, Real.sqrt_sq (norm_nonneg ψ)]
  ring

/-- Literal coordinate-word bounds of existing physical pointwise data have
    a common amplitude times the original full spin-state norm. -/
theorem physicalKSBoxPointwiseData_original_norm_word_bound
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A Csrc CH12 : ℝ} {ψ : SpinSpace 2}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A (Csrc * ‖ψ‖) (CH12 * ‖ψ‖^2))
    (hH12 : 0 ≤ CH12) :
    ∀ (w : List (Fin 4 ⊕ Fin 3)) p,
      p ∈ rectangularOpenBox (0,t0) (1/512) (1/512) →
      ‖complexDirectionalWordDeriv productCoordinateDirection f w p‖ ≤
        (physicalKSPointwiseAmplitude M A Csrc CH12 * ‖ψ‖) *
          (physicalKSPointwiseRate M A)^w.length * (w.length.factorial : ℝ) := by
  intro w p hp
  have hb := hdata.2.2 w p hp
  rwa [physicalKSPointwiseAmplitude_original_norm ψ M A Csrc CH12 hH12] at hb

/-- Original-state norm control of the genuine physical factorial jets in
    every recovered nuclear and pair KS chart, at every 0<epsilon<=1/4. -/
theorem coulomb_spin_physical_original_norm_factorial (Z E : ℝ) :
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
            PhysicalKSBoxFactorialData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              t0 M A (Csrc * ‖ψ‖) (CH12 * ‖ψ‖^2)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxFactorialData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              t0 M A (Csrc * ‖ψ‖) (CH12 * ‖ψ‖^2)) := by
  classical
  obtain ⟨C_H, M, A, hCH, hM, hA, hgain⟩ := scalar_coulomb_all_physical_box_factorial Z E
  obtain ⟨C_L, hLipGain⟩ := coulomb_spin_local_lipschitz_original_norm_bound
    (by norm_num : 0 < 2) Z E 1
  let Csrc : ℝ := M * coulombMoserBoundCoefficient 2 Z E * Real.sqrt physicalKSUniformSourceVolume
  let CH12 : ℝ := C_H * ((C_L : ℝ)^2 + (coulombMoserBoundCoefficient 2 Z E)^2)
  have hCH0 : 0 ≤ C_H := zero_le_one.trans hCH
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMoser0 : 0 ≤ coulombMoserBoundCoefficient 2 Z E :=
    (coulombMoserBoundCoefficient_pos 2 Z E).le
  have hCsrc : 0 ≤ Csrc := by dsimp [Csrc]; positivity
  have hCH12 : 0 ≤ CH12 := by dsimp [CH12]; positivity
  refine ⟨M, A, C_L, Csrc, CH12, hM, hA, hCsrc, hCH12, ?_⟩
  intro ψ hgraph
  obtain ⟨u, hu, hAE, hperm, hbound, hLipClosed⟩ := hLipGain ψ hgraph
  have hLip (σ : SpinConfiguration 2) :
      LipschitzOnWith (C_L * ‖ψ‖₊) (u σ) (ball 0 1) :=
    (hLipClosed σ).mono ball_subset_closedBall
  have hσAE (σ : SpinConfiguration 2) : (ψ σ : Configuration 2 → ℂ) =ᵐ[volume] u σ :=
    hAE.mono fun x hx => hx σ
  have hF0 : 0 ≤ spinOriginFactorialSourceBudget M u :=
    spinOriginFactorialSourceBudget_nonneg hM0 u
  have hW : 0 ≤ spinOriginH12Budget C_H (C_L * ‖ψ‖₊) u := by
    unfold spinOriginH12Budget
    positivity
  have hF : spinOriginFactorialSourceBudget M u ≤ Csrc * ‖ψ‖ := by
    exact spin_origin_source_original_norm_le hM0 hbound
  have hH : spinOriginH12Budget C_H (C_L * ‖ψ‖₊) u ≤ CH12 * ‖ψ‖^2 := by
    exact spin_origin_h12_original_norm_le C_L hCH0 hbound
  have hscale (ε : ℝ) (hε : ε ≤ 1/4) : ε ≤ min 1 ((1 : ℝ)/4) := by
    norm_num
    exact hε
  refine ⟨u, hu, hLip, hAE, hperm, hbound, ?_, ?_⟩
  · intro ε hε hlim σ i t0 ht0
    have hdata := (hgain (ψ σ) (hgraph.2.2 σ) (u σ) (hu σ).continuous
      (hσAE σ) (C_L * ‖ψ‖₊) 1 ε (hLip σ) hε (hscale ε hlim)).1 i t0 ht0
    exact (hdata.mono_spin_budget hCH hM hA).mono_source_budget hM hA hF0 hW hF hH
  · intro ε hε hlim σ t0 ht0
    have hdata := (hgain (ψ σ) (hgraph.2.2 σ) (u σ) (hu σ).continuous
      (hσAE σ) (C_L * ‖ψ‖₊) 1 ε (hLip σ) hε (hscale ε hlim)).2 t0 ht0
    exact (hdata.mono_spin_budget hCH hM hA).mono_source_budget hM hA hF0 hW hF hH

/-- The identical actual KS pullbacks are smooth and analytic and obey
    pointwise coordinate-word factorial bounds with original-state budgets. -/
theorem coulomb_spin_physical_original_norm_pointwise (Z E : ℝ) :
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
            PhysicalKSBoxPointwiseData
              ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              t0 M A (Csrc * ‖ψ‖) (CH12 * ‖ψ‖^2)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1/4 →
          ∀ (σ : SpinConfiguration 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxPointwiseData
              ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              t0 M A (Csrc * ‖ψ‖) (CH12 * ‖ψ‖^2)) := by
  obtain ⟨M, A, C_L, Csrc, CH12, hM, hA, hsrc, hH12, hgain⟩ :=
    coulomb_spin_physical_original_norm_factorial Z E
  refine ⟨M, A, C_L, Csrc, CH12, hM, hA, hsrc, hH12, ?_⟩
  intro ψ hgraph
  obtain ⟨u, hu, hLip, hAE, hperm, hbound, hN, hP⟩ := hgain ψ hgraph
  have hF0 : 0 ≤ Csrc * ‖ψ‖ := mul_nonneg hsrc (norm_nonneg ψ)
  refine ⟨u, hu, hLip, hAE, hperm, hbound, ?_, ?_⟩
  · intro ε hε hlim σ i t0 ht0
    have hc : Continuous
        ((originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) :=
      ((originScaledDifference_continuous (hu σ).continuous ε).comp
        (nuclearKSLift_contDiff i).continuous).comp (physicalSpectatorReindexAt i).symm.continuous
    exact physicalKSBoxFactorialData_to_pointwise (hN ε hε hlim σ i t0 ht0)
      hc.continuousOn hA hF0
  · intro ε hε hlim σ t0 ht0
    have hc : Continuous
        ((originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) :=
      ((originScaledDifference_continuous (hu σ).continuous ε).comp
        TheoremT.Continuum.pairKSLift_contDiff.continuous).comp (physicalSpectatorReindexAt (0 : Fin 2)).symm.continuous
    exact physicalKSBoxFactorialData_to_pointwise (hP ε hε hlim σ t0 ht0)
      hc.continuousOn hA hF0

#print axioms physicalKSFactorialAmplitude_original_norm
#print axioms physicalKSPointwiseAmplitude_original_norm
#print axioms physicalKSBoxPointwiseData_original_norm_word_bound
#print axioms coulomb_spin_physical_original_norm_factorial
#print axioms coulomb_spin_physical_original_norm_pointwise
end ManyBody.S8
