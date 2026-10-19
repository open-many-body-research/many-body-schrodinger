import KSCommonAnnulusFactorialJets_v1
import KSScaledFactorialWordBounds_v1

/-! The same constants control actual ordered physical coordinate words,
mixed Y/T words, and squared L2 budgets of the normalized source on every
measurable subregion. They precede all three charts and all unit centers.
No derivative or regularity of a solution is asserted. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

def KSScaledFactorialWordControl {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : ℝ → Space κ → ℝ) (K : Set (Space κ)) (C A : ℝ) : Prop :=
  ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
    (∀ w : List (Fin 4 ⊕ κ), ∀ q ∈ K,
      |directionalWordDeriv productCoordinateDirection (b eps) w q| ≤
        C*A^w.length*(w.length.factorial : ℝ) ∧
      |directionalWordDeriv productCoordinateDirection (fun p => eps*b eps p) w q| ≤
        eps*(C*A^w.length*(w.length.factorial : ℝ))) ∧
    ∀ (a : List (Fin 4)) (t : List κ),
      (∀ q ∈ K,
        |directionalWordDeriv yDir (spectatorWordDeriv (b eps) t) a q| ≤
          C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) ∧
        |directionalWordDeriv yDir (spectatorWordDeriv (fun p => eps*b eps p) t) a q| ≤
          eps*(C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ))) ∧
      ∀ a0 : ℂ, ∀ S : Set (Space κ), MeasurableSet S → S ⊆ K →
        RegionL2Budget
          (fun p => directionalWordDeriv yDir (spectatorWordDeriv (b eps) t) a p • (-a0)) S
          ((C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ))^2 *
            ‖a0‖^2 * (volume S).toReal)

theorem ksScaledFactorialWordControl_of_jets {κ : Type} [Fintype κ] [DecidableEq κ]
    {b : ℝ → Space κ → ℝ} {K Ω : Set (Space κ)} {C A : ℝ}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hb : ∀ eps : ℝ, ContDiffOn ℝ ∞ (b eps) Ω)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hjets : KSScaledFactorialJetControl b K C A) :
    KSScaledFactorialWordControl b K C A := by
  intro eps heps heps1
  have hs : ContDiffOn ℝ ∞ (fun p => eps*b eps p) Ω := by
    simpa only [smul_eq_mul] using (hb eps).const_smul eps
  refine ⟨?_,?_⟩
  · intro w q hq
    obtain ⟨hu,hscaled,_⟩ := hjets eps heps heps1 w.length q hq
    exact ⟨(directionalWordDeriv_abs_le_iteratedFDeriv productCoordinateDirection
      (fun j => (productCoordinateDirection_norm j).le) hΩ (hb eps) w (hKΩ hq)).trans hu,
      (directionalWordDeriv_abs_le_iteratedFDeriv productCoordinateDirection
      (fun j => (productCoordinateDirection_norm j).le) hΩ hs w (hKΩ hq)).trans hscaled⟩
  · intro a t
    have hword (q : Space κ) (hq : q ∈ K) :
        |directionalWordDeriv yDir (spectatorWordDeriv (b eps) t) a q| ≤
          C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) :=
      (mixedWordDeriv_abs_le_iteratedFDeriv hΩ (hb eps) a t (hKΩ hq)).trans
        (hjets eps heps heps1 (a.length+t.length) q hq).1
    refine ⟨?_,?_⟩
    · intro q hq
      exact ⟨hword q hq,(mixedWordDeriv_abs_le_iteratedFDeriv hΩ hs a t (hKΩ hq)).trans
        (hjets eps heps heps1 (a.length+t.length) q hq).2.1⟩
    · intro a0 S hS hSK
      have hfinite : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
      simpa only [norm_neg] using smooth_mixed_source_region_budget hΩ (hb eps) (-a0) a t
        hS (hSK.trans hKΩ) hfinite
        (show 0 ≤ C*A^(a.length+t.length)*((a.length+t.length).factorial : ℝ) from by positivity)
        (fun q hq => hword q (hSK hq))

theorem ksScaledFactorialWordControl_subset {κ : Type} [Fintype κ] [DecidableEq κ]
    {b : ℝ → Space κ → ℝ} {S K : Set (Space κ)} {C A : ℝ}
    (h : KSScaledFactorialWordControl b K C A) (hSK : S ⊆ K) :
    KSScaledFactorialWordControl b S C A := by
  intro eps heps heps1
  obtain ⟨hword,hmixed⟩ := h eps heps heps1
  refine ⟨fun w q hq => hword w q (hSK hq),?_⟩
  intro a t
  exact ⟨fun q hq => (hmixed a t).1 q (hSK hq),
    fun a0 U hU hUS => (hmixed a t).2 a0 U hU (hUS.trans hSK)⟩

theorem ksScaledFactorialWordControl_physical_word (i : Fin 2)
    {b : ℝ → NuclearKSSpace i → ℝ} {K : Set (NuclearKSSpace i)} {C A : ℝ}
    (h : KSScaledFactorialWordControl b K C A)
    (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (w : List (Fin 4 ⊕ Fin 3)) {q : NuclearKSSpace i} (hq : q ∈ K) :
    |directionalWordDeriv productCoordinateDirection (b eps)
      (w.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm)) q| ≤
        C*A^w.length*(w.length.factorial : ℝ) ∧
    |directionalWordDeriv productCoordinateDirection (fun p => eps*b eps p)
      (w.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm)) q| ≤
        eps*(C*A^w.length*(w.length.factorial : ℝ)) := by
  simpa only [List.length_map] using (h eps heps heps1).1
    (w.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm)) q hq

theorem ksCommonAnnulus_uniform_factorial_jet_word_control (Z E : ℝ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      (∀ i : Fin 2,
        KSScaledFactorialJetControl (fun eps => nuclearKSPotential i Z (eps*E))
          (ksCommonAnnulusRegionAt i) C A ∧
        KSScaledFactorialWordControl (fun eps => nuclearKSPotential i Z (eps*E))
          (ksCommonAnnulusRegionAt i) C A) ∧
      (KSScaledFactorialJetControl (fun eps => pairKSPotential Z (eps*E))
          ksCommonAnnulusRegion C A ∧
        KSScaledFactorialWordControl (fun eps => pairKSPotential Z (eps*E))
          ksCommonAnnulusRegion C A) := by
  obtain ⟨C,A,hC,hA,hN,hP⟩ := ksCommonAnnulus_uniform_factorial_jets Z E
  refine ⟨C,A,hC,hA,?_,hP,?_⟩
  · intro i
    refine ⟨hN i,?_⟩
    apply ksScaledFactorialWordControl_of_jets (ksCommonAnnulusRegionAt_isCompact i)
      (nuclearKSCoefficientPatch_isOpen i) (ksCommonAnnulusRegionAt_subset_nuclear_patch i)
      _ (zero_le_one.trans hC) (zero_le_one.trans hA) (hN i)
    intro eps q hq
    exact (nuclearKSPotential_contDiffAt i Z (eps*E) hq).contDiffWithinAt
  · apply ksScaledFactorialWordControl_of_jets ksCommonAnnulusRegion_isCompact
      pairKSCoefficientPatch_isOpen ksCommonAnnulusRegion_subset_pair_patch
      _ (zero_le_one.trans hC) (zero_le_one.trans hA) hP
    intro eps q hq
    exact (pairKSPotential_contDiffAt Z (eps*E) hq).contDiffWithinAt

theorem ksCommonAnnulus_uniform_factorial_physical_box_data (Z E : ℝ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      (∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
        KSScaledFactorialJetControl (fun eps => nuclearKSPotential i Z (eps*E))
          (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox (0,t0) (1/64) (1/64)) C A ∧
        KSScaledFactorialWordControl (fun eps => nuclearKSPotential i Z (eps*E))
          (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox (0,t0) (1/64) (1/64)) C A) ∧
      (∀ t0 : Position, ‖t0‖ = 1 →
        KSScaledFactorialJetControl (fun eps => pairKSPotential Z (eps*E))
          (physicalSpectatorReindexAt (0 : Fin 2) ⁻¹'
            rectangularOpenBox (0,t0) (1/64) (1/64)) C A ∧
        KSScaledFactorialWordControl (fun eps => pairKSPotential Z (eps*E))
          (physicalSpectatorReindexAt (0 : Fin 2) ⁻¹'
            rectangularOpenBox (0,t0) (1/64) (1/64)) C A) := by
  obtain ⟨C,A,hC,hA,hN,hP⟩ := ksCommonAnnulus_uniform_factorial_jet_word_control Z E
  refine ⟨C,A,hC,hA,?_,?_⟩
  · intro i t0 ht0
    have hS := physical_initialization_box_subset_commonAnnulusAt i ht0
    exact ⟨ksScaledFactorialJetControl_subset (hN i).1 hS,
      ksScaledFactorialWordControl_subset (hN i).2 hS⟩
  · intro t0 ht0
    have hS := physical_initialization_box_subset_commonAnnulusAt (0 : Fin 2) ht0
    exact ⟨ksScaledFactorialJetControl_subset hP.1 hS,
      ksScaledFactorialWordControl_subset hP.2 hS⟩

end TheoremT.Continuum
