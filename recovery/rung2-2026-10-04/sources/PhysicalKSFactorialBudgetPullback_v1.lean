import PhysicalSpectatorFactorialWords_v1
import ComplexWordRealAmplitudeBudget_v1
import PhysicalKSUniformSourceVolume_v1

/-! Actual full-word coefficient and complex source budgets after physical
spectator reindexing. A fixed finite volume constant makes the source factor
independent of the unit center and derivative order. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem physicalKS_factorial_budget_pullback (i : Fin 2)
    {Ω : Set (NuclearKSSpace i)} (hΩ : IsOpen Ω)
    {b : ℝ → NuclearKSSpace i → ℝ}
    (hb : ∀ eps, ContDiffOn ℝ ∞ (b eps) Ω)
    {t0 : Position} (ht0 : ‖t0‖ = 1)
    (hboxΩ : physicalSpectatorReindexAt i ⁻¹'
      rectangularOpenBox (0,t0) (1/64) (1/64) ⊆ Ω)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hcontrol : KSScaledFactorialWordControl b
      (physicalSpectatorReindexAt i ⁻¹'
        rectangularOpenBox (0,t0) (1/64) (1/64)) C A)
    (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (a0 : ℂ) :
    (∀ w : List (Fin 4 ⊕ Fin 3),
      ∀ p ∈ rectangularOpenBox (0,t0) (1/128) (1/128),
      |directionalWordDeriv productCoordinateDirection
        ((fun q => eps*b eps q) ∘ (physicalSpectatorReindexAt i).symm) w p| ≤
        C*A^w.length*(w.length.factorial : ℝ)) ∧
    (∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection
        ((fun q => b eps q • (-a0)) ∘ (physicalSpectatorReindexAt i).symm) w)
        (rectangularOpenBox (0,t0) (1/128) (1/128))
        ((C*‖a0‖*Real.sqrt physicalKSUniformSourceVolume*
          A^w.length*(w.length.factorial : ℝ))^2)) := by
  let O := rectangularOpenBox (0,t0) (1/64) (1/64)
  let S := rectangularOpenBox (0,t0) (1/128) (1/128)
  have hO : IsOpen O := rectangularOpenBox_isOpen (0,t0) _ _
  have hS : MeasurableSet S := (rectangularOpenBox_isOpen (0,t0) _ _).measurableSet
  have hSO : S ⊆ O := (rectangularOpenBox_subset_closedBox (0,t0) _ _).trans
    (rectangularClosedBox_subset_openBox (0,t0) (by norm_num) (by norm_num))
  have hpull {p : Space (Fin 3)} (hp : p ∈ O) :
      (physicalSpectatorReindexAt i).symm p ∈
        physicalSpectatorReindexAt i ⁻¹' O := by
    simpa only [Set.mem_preimage,LinearIsometryEquiv.apply_symm_apply] using hp
  have hbcan : ContDiffOn ℝ ∞ (b eps ∘ (physicalSpectatorReindexAt i).symm) O :=
    (hb eps).comp (physicalSpectatorReindexAt i).symm.contDiff.contDiffOn
      (fun p hp => hboxΩ (hpull hp))
  have hbs : ContDiffOn ℝ ∞ (fun q => eps*b eps q) Ω := by
    simpa only [smul_eq_mul] using (hb eps).const_smul eps
  have hword (w : List (Fin 4 ⊕ Fin 3)) {p : Space (Fin 3)} (hp : p ∈ O) :
      |directionalWordDeriv productCoordinateDirection
        (b eps ∘ (physicalSpectatorReindexAt i).symm) w p| ≤
        C*A^w.length*(w.length.factorial : ℝ) := by
    rw [physicalSpectatorReindexAt_symm_word i hΩ (hb eps) w (hboxΩ (hpull hp))]
    exact (ksScaledFactorialWordControl_physical_word i hcontrol eps heps heps1 w
      (hpull hp)).1
  refine ⟨?_,?_⟩
  · intro w p hp
    rw [physicalSpectatorReindexAt_symm_word i hΩ hbs w (hboxΩ (hpull (hSO hp)))]
    exact ((ksScaledFactorialWordControl_physical_word i hcontrol eps heps heps1 w
      (hpull (hSO hp))).2).trans (mul_le_of_le_one_left (by positivity) heps1)
  · intro w
    obtain ⟨hfinite,hvolume⟩ := physicalKS_box_volume_bound ht0
    have hr := complex_word_real_amplitude_region_budget productCoordinateDirection hO
      hbcan (-a0) w hS hSO hfinite (show 0 ≤ C*A^w.length*(w.length.factorial : ℝ) by positivity)
      (fun p hp => hword w (hSO hp))
    change RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection
      (fun p => (b eps ∘ (physicalSpectatorReindexAt i).symm) p • (-a0)) w) S _
    refine ⟨hr.1,hr.2.trans ?_⟩
    simp only [norm_neg]
    calc
      _ ≤ (C*A^w.length*(w.length.factorial : ℝ))^2*‖a0‖^2*
          physicalKSUniformSourceVolume :=
        mul_le_mul_of_nonneg_left hvolume (by positivity)
      _ = _ := by
        simp only [mul_pow,Real.sq_sqrt physicalKSUniformSourceVolume_nonneg]
        ring

end TheoremT.Continuum
