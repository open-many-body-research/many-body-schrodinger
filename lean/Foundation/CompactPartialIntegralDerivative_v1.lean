import CompactPartialIntegralSupport_v1

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum
variable {Y T F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasureOnCompacts μ]

theorem compact_joint_exists_integrable_bound {G : Y × T → F} (hG : Continuous G)
    (hc : HasCompactSupport G) :
    ∃ b : T → ℝ, Integrable b μ ∧ ∀ y t, ‖G (y,t)‖ ≤ b t := by
  classical
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hG
  let K : Set T := Prod.snd '' tsupport G
  have hK : IsCompact K := hc.isCompact.image continuous_snd
  refine ⟨K.indicator (fun _ => C), (integrable_indicator_iff hK.measurableSet).mpr
    (integrableOn_const (C := C) (μ := μ) hK.measure_ne_top), ?_⟩
  intro y t
  by_cases ht : t ∈ K
  · simpa only [Set.indicator_of_mem ht] using hC (y,t)
  · have hz : G (y,t)=0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      exact ht ⟨(y,t),hp,rfl⟩
    simp only [Set.indicator_of_notMem ht,hz,norm_zero,le_refl]

theorem compactPartialIntegral_hasFDerivAt {G : Y × T → F}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (y : Y) :
    HasFDerivAt (compactPartialIntegral (μ := μ) G)
      (compactPartialIntegral (μ := μ) (firstParameterFDeriv G) y) y := by
  have hD := firstParameterFDeriv_contDiff hG
  have hcD := firstParameterFDeriv_hasCompactSupport hc
  obtain ⟨b,hb,hbound⟩ := compact_joint_exists_integrable_bound (μ := μ) hD.continuous hcD
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => G (y,t)) (F' := fun y t => firstParameterFDeriv G (y,t))
    (s := Set.univ) (bound := b) (by simp)
    (Filter.Eventually.of_forall (fun x => (compact_slice_integrable hG.continuous hc x).aestronglyMeasurable))
    (compact_slice_integrable hG.continuous hc y)
    (compact_slice_integrable hD.continuous hcD y).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t x _ => hbound x t)) hb
    (Filter.Eventually.of_forall (fun t x _ => firstParameterFDeriv_hasFDerivAt hG x t))

theorem compactPartialIntegral_fderiv {G : Y × T → F}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    fderiv ℝ (compactPartialIntegral (μ := μ) G) =
      compactPartialIntegral (μ := μ) (firstParameterFDeriv G) := by
  funext y
  exact (compactPartialIntegral_hasFDerivAt hG hc y).fderiv

#print axioms compact_joint_exists_integrable_bound
#print axioms compactPartialIntegral_hasFDerivAt
#print axioms compactPartialIntegral_fderiv
end TheoremT.Continuum
