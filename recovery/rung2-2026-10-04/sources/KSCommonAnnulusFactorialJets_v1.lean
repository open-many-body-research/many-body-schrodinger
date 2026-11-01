import KSScaledFactorialCoefficientBounds_v1
import KSCommonAnnulusPatchAll_v1

/-! One factorial majorant for the two nuclear charts and the pair chart,
chosen before scale, order, point, source amplitude, and unit physical center.
The bounds concern the actual coefficients and their normalized forcing only. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
open WeakGrushin

def KSScaledFactorialJetControl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (b : ℝ → X → ℝ) (K : Set X) (C A : ℝ) : Prop :=
  ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ k : ℕ, ∀ q ∈ K,
    ‖iteratedFDeriv ℝ k (b eps) q‖ ≤ C*A^k*(k.factorial : ℝ) ∧
    ‖iteratedFDeriv ℝ k (fun p => eps*b eps p) q‖ ≤ eps*(C*A^k*(k.factorial : ℝ)) ∧
    ∀ a0 : ℂ, ‖iteratedFDeriv ℝ k (fun p => b eps p • (-a0)) q‖ ≤
      (C*A^k*(k.factorial : ℝ))*‖a0‖

theorem ksScaledFactorialJetControl_mono {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {b : ℝ → X → ℝ} {K : Set X} {C0 A0 C A : ℝ}
    (hmajor : ∀ k : ℕ, C0*A0^k*(k.factorial : ℝ) ≤ C*A^k*(k.factorial : ℝ))
    (h : KSScaledFactorialJetControl b K C0 A0) :
    KSScaledFactorialJetControl b K C A := by
  intro eps heps heps1 k q hq
  obtain ⟨hb,hs,hf⟩ := h eps heps heps1 k q hq
  exact ⟨hb.trans (hmajor k),hs.trans (mul_le_mul_of_nonneg_left (hmajor k) heps),
    fun a0 => (hf a0).trans (mul_le_mul_of_nonneg_right (hmajor k) (norm_nonneg _))⟩

theorem ksScaledFactorialJetControl_subset {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {b : ℝ → X → ℝ} {S K : Set X} {C A : ℝ}
    (h : KSScaledFactorialJetControl b K C A) (hS : S ⊆ K) :
    KSScaledFactorialJetControl b S C A :=
  fun eps heps heps1 k q hq => h eps heps heps1 k q (hS hq)

theorem ksCommonAnnulus_uniform_factorial_jets (Z E : ℝ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      (∀ i : Fin 2, KSScaledFactorialJetControl
        (fun eps => nuclearKSPotential i Z (eps*E)) (ksCommonAnnulusRegionAt i) C A) ∧
      KSScaledFactorialJetControl (fun eps => pairKSPotential Z (eps*E))
        ksCommonAnnulusRegion C A := by
  classical
  have hn (i : Fin 2) : ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      KSScaledFactorialJetControl (fun eps => nuclearKSPotential i Z (eps*E))
        (ksCommonAnnulusRegionAt i) C A := by
    obtain ⟨C,A,hC,hA,hb⟩ := nuclearKS_uniform_factorial_scaled_jets i Z E
      (ksCommonAnnulusRegionAt_isCompact i) (ksCommonAnnulusRegionAt_subset_nuclear_patch i)
    refine ⟨C,A,hC,hA,?_⟩
    intro eps heps heps1 k q hq
    obtain ⟨hbare,hscaled,hsource⟩ := hb eps heps heps1 k q hq
    refine ⟨hbare,?_,hsource⟩
    change ‖iteratedFDeriv ℝ k (epsilonNuclearKSPotential i eps Z E) q‖ ≤ _
    exact hscaled
  choose CN AN hCN hAN hN using hn
  obtain ⟨CP,AP,hCP,hAP,hP⟩ := pairKS_uniform_factorial_scaled_jets Z E
    ksCommonAnnulusRegion_isCompact ksCommonAnnulusRegion_subset_pair_patch
  have hp : KSScaledFactorialJetControl (fun eps => pairKSPotential Z (eps*E))
      ksCommonAnnulusRegion CP AP := by
    intro eps heps heps1 k q hq
    obtain ⟨hbare,hscaled,hsource⟩ := hP eps heps heps1 k q hq
    refine ⟨hbare,?_,hsource⟩
    change ‖iteratedFDeriv ℝ k (epsilonPairKSPotential eps Z E) q‖ ≤ _
    exact hscaled
  let Cs : Fin 2 ⊕ Unit → ℝ := Sum.elim CN (fun _ => CP)
  let As : Fin 2 ⊕ Unit → ℝ := Sum.elim AN (fun _ => AP)
  have hCs : ∀ j ∈ (Finset.univ : Finset (Fin 2 ⊕ Unit)), 0 ≤ Cs j := by
    intro j _
    cases j with
    | inl i => exact zero_le_one.trans (hCN i)
    | inr u => exact zero_le_one.trans hCP
  have hAs : ∀ j ∈ (Finset.univ : Finset (Fin 2 ⊕ Unit)), 0 ≤ As j := by
    intro j _
    cases j with
    | inl i => exact zero_le_one.trans (hAN i)
    | inr u => exact zero_le_one.trans hAP
  obtain ⟨hC,hA,hmajor⟩ := finite_factorial_common_bound Finset.univ Cs As hCs hAs
  refine ⟨finiteFactorialC Finset.univ Cs,finiteFactorialA Finset.univ As,hC,hA,?_,?_⟩
  · intro i
    exact ksScaledFactorialJetControl_mono
      (fun k => hmajor (Sum.inl i) (Finset.mem_univ _) k) (hN i)
  · exact ksScaledFactorialJetControl_mono
      (fun k => hmajor (Sum.inr ()) (Finset.mem_univ _) k) hp

theorem ksCommonAnnulus_uniform_factorial_physical_boxes (Z E : ℝ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      (∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
        KSScaledFactorialJetControl (fun eps => nuclearKSPotential i Z (eps*E))
          (physicalSpectatorReindexAt i ⁻¹' rectangularOpenBox (0,t0) (1/64) (1/64)) C A) ∧
      (∀ t0 : Position, ‖t0‖ = 1 →
        KSScaledFactorialJetControl (fun eps => pairKSPotential Z (eps*E))
          (physicalSpectatorReindexAt (0 : Fin 2) ⁻¹'
            rectangularOpenBox (0,t0) (1/64) (1/64)) C A) := by
  obtain ⟨C,A,hC,hA,hN,hP⟩ := ksCommonAnnulus_uniform_factorial_jets Z E
  refine ⟨C,A,hC,hA,?_,?_⟩
  · intro i t0 ht0
    exact ksScaledFactorialJetControl_subset (hN i)
      (physical_initialization_box_subset_commonAnnulusAt i ht0)
  · intro t0 ht0
    exact ksScaledFactorialJetControl_subset hP
      (physical_initialization_box_subset_commonAnnulusAt (0 : Fin 2) ht0)

end TheoremT.Continuum
