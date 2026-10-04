import ConfigurationL2Dominated_v1
import ManyBody.S8.Internal.PhysicalDistanceCompositionGeometry

/-! Actual compact-domain domination supplies the L2 limit class and strong
convergence. Limit L2 membership is derived from genuine AE convergence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_compact_dominated_L2_limit {N : ℕ}
    {K : Set (Configuration N)} (hK : IsCompact K)
    {b : Configuration N → ℝ} (hb : MemLp b 2 (volume.restrict K))
    {F : ℕ → Configuration N → ℂ} {f : Configuration N → ℂ}
    (hF : ∀ n, AEStronglyMeasurable (F n) volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖≤‖K.indicator b x‖)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ∃ hFn : ∀ n, MemLp (F n) 2 volume, ∃ hf : MemLp f 2 volume,
      Tendsto (fun n => (hFn n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  have hb' : MemLp (K.indicator b) 2 volume :=
    (memLp_indicator_iff_restrict hK.isClosed.measurableSet).mpr hb
  have hFn (n : ℕ) : MemLp (F n) 2 volume := hb'.norm.mono' (hF n) (hbound n)
  have hfm : AEStronglyMeasurable f volume := aestronglyMeasurable_of_tendsto_ae atTop hF hlim
  have hfb : ∀ᵐ x ∂volume, ‖f x‖≤‖K.indicator b x‖ := by
    filter_upwards [ae_all_iff.mpr hbound,hlim] with x hx hxt
    exact le_of_tendsto hxt.norm (Eventually.of_forall hx)
  have hf : MemLp f 2 volume := hb'.norm.mono' hfm hfb
  exact ⟨hFn,hf,configuration_toLp_tendsto_dominated hFn hf hb' hbound hfb hlim⟩

theorem physical_compact_inverse_distance_domination_memLp
    {K : Set (Configuration 2)} (hK : IsCompact K) :
    MemLp (K.indicator (fun x => 1+physicalInverseDistanceBudget x)) 2 volume := by
  have hc : MemLp (K.indicator (fun _ : Configuration 2 => (1:ℝ))) 2 volume :=
    memLp_indicator_const 2 hK.isClosed.measurableSet 1 (Or.inr hK.measure_lt_top.ne)
  have hb : MemLp (K.indicator physicalInverseDistanceBudget) 2 volume :=
    (memLp_indicator_iff_restrict hK.isClosed.measurableSet).mpr
      (physical_inverse_distance_budget_memLp_on_compact hK)
  convert hc.add hb using 1
  ext x
  simp only [Set.indicator_add, Pi.add_apply]

#print axioms physical_compact_dominated_L2_limit
#print axioms physical_compact_inverse_distance_domination_memLp
end ManyBody.S8
