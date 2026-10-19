import PhysicalKSFactorialBudgetPullback_v1

/-! One pair of constants controls the actual canonical physical coefficient
words and all complex source-word L2 budgets in both nuclear charts and the
pair chart. Constants precede all unit centers, scales in [0,1], amplitudes
and derivative words. These are coefficient/source bounds, not solution bounds. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
open WeakGrushin

theorem ksCommon_physical_factorial_budgets (Z E : ℝ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      (∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
        ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ a0 : ℂ,
        (∀ w : List (Fin 4 ⊕ Fin 3),
          ∀ p ∈ rectangularOpenBox (0,t0) (1/128) (1/128),
          |directionalWordDeriv productCoordinateDirection
            (epsilonNuclearKSPotential i eps Z E ∘ (physicalSpectatorReindexAt i).symm) w p| ≤
            C*A^w.length*(w.length.factorial : ℝ)) ∧
        (∀ w : List (Fin 4 ⊕ Fin 3),
          RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection
            ((fun q => nuclearKSPotential i Z (eps*E) q • (-a0)) ∘
              (physicalSpectatorReindexAt i).symm) w)
            (rectangularOpenBox (0,t0) (1/128) (1/128))
            ((C*‖a0‖*Real.sqrt physicalKSUniformSourceVolume*
              A^w.length*(w.length.factorial : ℝ))^2))) ∧
      (∀ t0 : Position, ‖t0‖ = 1 →
        ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ a0 : ℂ,
        (∀ w : List (Fin 4 ⊕ Fin 3),
          ∀ p ∈ rectangularOpenBox (0,t0) (1/128) (1/128),
          |directionalWordDeriv productCoordinateDirection
            (epsilonPairKSPotential eps Z E ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) w p| ≤
            C*A^w.length*(w.length.factorial : ℝ)) ∧
        (∀ w : List (Fin 4 ⊕ Fin 3),
          RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection
            ((fun q => pairKSPotential Z (eps*E) q • (-a0)) ∘
              (physicalSpectatorReindexAt (0 : Fin 2)).symm) w)
            (rectangularOpenBox (0,t0) (1/128) (1/128))
            ((C*‖a0‖*Real.sqrt physicalKSUniformSourceVolume*
              A^w.length*(w.length.factorial : ℝ))^2))) := by
  obtain ⟨C,A,hC,hA,hN,hP⟩ := ksCommonAnnulus_uniform_factorial_physical_box_data Z E
  refine ⟨C,A,hC,hA,?_,?_⟩
  · intro i t0 ht0 eps heps heps1 a0
    exact physicalKS_factorial_budget_pullback i (nuclearKSCoefficientPatch_isOpen i)
      (fun eps p hp => (nuclearKSPotential_contDiffAt i Z (eps*E) hp).contDiffWithinAt)
      ht0 (physical_initialization_box_nuclear_patchAt i ht0)
      (zero_le_one.trans hC) (zero_le_one.trans hA) (hN i t0 ht0).2
      eps heps heps1 a0
  · intro t0 ht0 eps heps heps1 a0
    exact physicalKS_factorial_budget_pullback (0 : Fin 2) pairKSCoefficientPatch_isOpen
      (fun eps p hp => (pairKSPotential_contDiffAt Z (eps*E) hp).contDiffWithinAt)
      ht0 ((physical_initialization_box_subset_commonAnnulusAt (0 : Fin 2) ht0).trans
        ksCommonAnnulusRegion_subset_pair_patch)
      (zero_le_one.trans hC) (zero_le_one.trans hA) (hP t0 ht0).2
      eps heps heps1 a0

end TheoremT.Continuum
