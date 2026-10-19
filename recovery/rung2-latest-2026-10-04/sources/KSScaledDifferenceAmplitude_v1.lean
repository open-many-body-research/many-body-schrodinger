import LocallyLipschitzScaledDifference_v1
import KSChartImageNorm_v1

/-! Uniform P9 amplitude and compact restricted L2 bounds for the actual
normalized difference composed with the unchanged physical KS lifts. -/
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology NNReal
namespace TheoremT.Continuum

theorem originScaledDifference_norm_le_two_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} {L : ℝ≥0} {R ε : ℝ}
    (hR : 0 < R) (hg : LipschitzOnWith L g (ball 0 R))
    (hε : 0 < ε) (hεR : ε ≤ R / 4) {x : E} (hx : ‖x‖ < 2) :
    ‖originScaledDifference g ε x‖ ≤ 2 * (L : ℝ) := by
  have hscaled : ε * ‖x‖ < R := by nlinarith
  have hh := originScaledDifference_norm_le hR hg hε hscaled
  nlinarith [L.property]

theorem nuclearKS_scaled_difference_amplitude {N : ℕ} (i : Fin N)
    {g : Configuration N → ℂ} {L : ℝ≥0} {R ε : ℝ}
    (hR : 0 < R) (hg : LipschitzOnWith L g (ball 0 R))
    (hε : 0 < ε) (hεR : ε ≤ R / 4) (q : NuclearKSSpace i)
    (hy : ‖q.1‖ ≤ (1/4 : ℝ)) (ht : ‖q.2‖ ≤ (5/4 : ℝ)) :
    ‖originScaledDifference g ε (nuclearKSLift i q)‖ ≤ 2 * (L : ℝ) :=
  originScaledDifference_norm_le_two_lipschitz hR hg hε hεR
    (nuclearKSLift_norm_lt_two i q hy ht)

theorem pairKS_scaled_difference_amplitude
    {g : Configuration 2 → ℂ} {L : ℝ≥0} {R ε : ℝ}
    (hR : 0 < R) (hg : LipschitzOnWith L g (ball 0 R))
    (hε : 0 < ε) (hεR : ε ≤ R / 4) (q : PairKSSpace)
    (hy : ‖q.1‖ ≤ (1/4 : ℝ)) (ht : ‖q.2‖ ≤ (5/4 : ℝ)) :
    ‖originScaledDifference g ε (pairKSLift q)‖ ≤ 2 * (L : ℝ) :=
  originScaledDifference_norm_le_two_lipschitz hR hg hε hεR
    (pairKSLift_norm_lt_two q hy ht)

theorem continuousOn_compact_integral_norm_sq_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) {f : X → ℂ} (hf : ContinuousOn f K)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ K, ‖f x‖ ≤ C) :
    (∫ x in K, ‖f x‖^2 ∂μ) ≤ C^2 * (μ K).toReal := by
  haveI : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hi : IntegrableOn (fun x => ‖f x‖^2) K μ :=
    (hf.norm.pow 2).integrableOn_compact hK
  calc
    (∫ x in K, ‖f x‖^2 ∂μ) ≤ ∫ _x in K, C^2 ∂μ := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound x hx) 2
    _ = C^2 * (μ K).toReal := by simp [Measure.real,mul_comm]

theorem nuclearKS_scaled_difference_compact_L2 {N : ℕ} (i : Fin N)
    {g : Configuration N → ℂ} (hgcont : Continuous g) {L : ℝ≥0} {R ε : ℝ}
    (hR : 0 < R) (hg : LipschitzOnWith L g (ball 0 R))
    (hε : 0 < ε) (hεR : ε ≤ R / 4)
    {K : Set (NuclearKSSpace i)} (hK : IsCompact K)
    (hbox : ∀ q ∈ K, ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2‖ ≤ (5/4 : ℝ)) :
    MemLp (originScaledDifference g ε ∘ nuclearKSLift i) 2 (volume.restrict K) ∧
    (∫ q in K, ‖originScaledDifference g ε (nuclearKSLift i q)‖^2) ≤
      (2 * (L : ℝ))^2 * (volume K).toReal := by
  have hc := (originScaledDifference_continuous hgcont ε).comp
    (nuclearKSLift_contDiff i).continuous
  refine ⟨product_continuousOn_locallyL2 (Ω := Set.univ) hc.continuousOn K hK
    (Set.subset_univ K),?_⟩
  apply continuousOn_compact_integral_norm_sq_le hK hc.continuousOn (by positivity)
  intro q hq
  exact nuclearKS_scaled_difference_amplitude i hR hg hε hεR q (hbox q hq).1 (hbox q hq).2

theorem pairKS_scaled_difference_compact_L2
    {g : Configuration 2 → ℂ} (hgcont : Continuous g) {L : ℝ≥0} {R ε : ℝ}
    (hR : 0 < R) (hg : LipschitzOnWith L g (ball 0 R))
    (hε : 0 < ε) (hεR : ε ≤ R / 4)
    {K : Set PairKSSpace} (hK : IsCompact K)
    (hbox : ∀ q ∈ K, ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2‖ ≤ (5/4 : ℝ)) :
    MemLp (originScaledDifference g ε ∘ pairKSLift) 2 (volume.restrict K) ∧
    (∫ q in K, ‖originScaledDifference g ε (pairKSLift q)‖^2) ≤
      (2 * (L : ℝ))^2 * (volume K).toReal := by
  have hc := (originScaledDifference_continuous hgcont ε).comp pairKSLift_contDiff.continuous
  refine ⟨product_continuousOn_locallyL2 (Ω := Set.univ) hc.continuousOn K hK
    (Set.subset_univ K),?_⟩
  apply continuousOn_compact_integral_norm_sq_le hK hc.continuousOn (by positivity)
  intro q hq
  exact pairKS_scaled_difference_amplitude hR hg hε hεR q (hbox q hq).1 (hbox q hq).2

#print axioms originScaledDifference_norm_le_two_lipschitz
#print axioms nuclearKS_scaled_difference_amplitude
#print axioms pairKS_scaled_difference_amplitude
#print axioms continuousOn_compact_integral_norm_sq_le
#print axioms nuclearKS_scaled_difference_compact_L2
#print axioms pairKS_scaled_difference_compact_L2
end TheoremT.Continuum
