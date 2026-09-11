import NormalizedRadialMeanTest_v1

/-! Actual smooth radial mean and physical fluctuation on Euclidean space.
The possible nonsmoothness of the norm at zero is handled by the proved
vanishing neighborhood inherited from the original punctured support. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def physicalRadialMean (f : E → ℂ) (x : E) : ℂ := normalizedRadialMean f ‖x‖

def physicalFluctuation (f : E → ℂ) (x : E) : ℂ := f x - physicalRadialMean f x

theorem physicalRadialMean_zero_not_tsupport {f : E → ℂ}
    (hz : (0 : E) ∉ tsupport f) : (0 : E) ∉ tsupport (physicalRadialMean f) := by
  intro h
  have hm := tsupport_comp_subset_preimage (normalizedRadialMean f) continuous_norm h
  apply normalizedRadialMean_zero_not_tsupport hz
  simpa only [mem_preimage, norm_zero] using hm

theorem physicalRadialMean_contDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hz : (0 : E) ∉ tsupport f) : ContDiff ℝ ∞ (physicalRadialMean f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (physicalRadialMean_zero_not_tsupport hz))
  · exact (normalizedRadialMean_contDiff hf).contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem physicalRadialMean_compact {f : E → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (physicalRadialMean f) := by
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport (normalizedRadialMean f)) from
    normalizedRadialMean_compact hc).isBounded.exists_norm_le
  have hs : Function.support (physicalRadialMean f) ⊆ Metric.closedBall (0 : E) R := by
    intro x hx
    have hm : ‖x‖ ∈ tsupport (normalizedRadialMean f) :=
      subset_tsupport _ hx
    have hb := hR ‖x‖ hm
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_norm] using hb
  exact (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs Metric.isClosed_closedBall)

theorem physicalFluctuation_zero_not_tsupport {f : E → ℂ}
    (hz : (0 : E) ∉ tsupport f) : (0 : E) ∉ tsupport (physicalFluctuation f) := by
  intro h
  rcases tsupport_sub f (physicalRadialMean f) h with h | h
  · exact hz h
  · exact physicalRadialMean_zero_not_tsupport hz h

theorem physicalFluctuation_contDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hz : (0 : E) ∉ tsupport f) : ContDiff ℝ ∞ (physicalFluctuation f) :=
  hf.sub (physicalRadialMean_contDiff hf hz)

theorem physicalFluctuation_compact {f : E → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (physicalFluctuation f) := hc.sub (physicalRadialMean_compact hc)

theorem physicalRadialMean_on_ray (f : E → ℂ) (w : Metric.sphere (0 : E) 1)
    {r : ℝ} (hr : 0 ≤ r) : physicalRadialMean f (r • w.val) = normalizedRadialMean f r := by
  rw [physicalRadialMean, norm_radius_smul_sphere, abs_of_nonneg hr]

theorem physicalFluctuation_on_ray (f : E → ℂ) (w : Metric.sphere (0 : E) 1)
    {r : ℝ} (hr : 0 ≤ r) :
    physicalFluctuation f (r • w.val) = f (r • w.val) - normalizedRadialMean f r := by
  rw [physicalFluctuation, physicalRadialMean_on_ray f w hr]

theorem physicalFluctuation_sphere_mean_zero (hdim : Module.finrank ℝ E = 3)
    {f : E → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    (∫ w : Metric.sphere (0 : E) 1, physicalFluctuation f (r • w.val) ∂sphereMeasure) = 0 := by
  simp_rw [physicalFluctuation_on_ray f _ hr]
  exact radial_fluctuation_mean_zero hdim hf r

#print axioms physicalRadialMean_contDiff
#print axioms physicalRadialMean_compact
#print axioms physicalFluctuation_contDiff
#print axioms physicalFluctuation_sphere_mean_zero
end TheoremT.Polar
