import CompactLocalFactorialBound_v1
import PowerSeriesLocalDerivativeBound_v1

/-! Actual analytic functions have common factorial bounds for their genuine
iterated Fréchet derivatives near a compact set. The analytic local estimate is
proved in the imported power-series module; compactness only assembles it.
The existence constants here do not constitute an effective extraction algorithm. -/
noncomputable section
open scoped Topology
namespace TheoremT.Continuum

theorem analyticOnNhd_compact_factorial_bound_nhds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} (hK : IsCompact K) {f : E → F} (hf : AnalyticOnNhd ℝ f K) :
    ∃ U : Set E, U ∈ 𝓝ˢ K ∧ ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ y ∈ U, ∀ k, ‖iteratedFDeriv ℝ k f y‖ ≤ C * A ^ k * (k.factorial : ℝ) := by
  apply compact_local_factorial_bound_uniform_nhds hK (fun k y => iteratedFDeriv ℝ k f y)
  intro x hx
  obtain ⟨r,hr,C,hC,A,hA,hbound⟩ := analyticAt_local_factorial_bound (hf x hx)
  exact ⟨Metric.ball x r,Metric.ball_mem_nhds x hr,C,A,hC,hA,hbound⟩

theorem analyticOnNhd_compact_factorial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} (hK : IsCompact K) {f : E → F} (hf : AnalyticOnNhd ℝ f K) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ x ∈ K, ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ C * A ^ k * (k.factorial : ℝ) := by
  obtain ⟨U,hU,C,A,hC,hA,hbound⟩ := analyticOnNhd_compact_factorial_bound_nhds hK hf
  exact ⟨C,A,hC,hA,fun x hx k => hbound x (subset_of_mem_nhdsSet hU hx) k⟩

#print axioms analyticOnNhd_compact_factorial_bound_nhds
#print axioms analyticOnNhd_compact_factorial_bound
end TheoremT.Continuum
