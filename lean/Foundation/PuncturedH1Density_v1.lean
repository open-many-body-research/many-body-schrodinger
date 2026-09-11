import PuncturedSmoothCore_v1

/-! Density of C_c^∞(R³ \ {0}) in the genuine one-electron weak H¹ graph.
All approximating values and derivatives are actual L² equivalence classes, and
the approximants also lie in the actual weak H² domain. The input is only H¹.
The existential stage selection is mathematical density, not an implemented solver. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem weakH1_punctured_smooth_compact_graph_approximation {f : SpatialL2 1}
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : Configuration 1 → ℂ, ∃ g : SpatialL2 1,
      ∃ dg : Coordinate 1 → SpatialL2 1,
      ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ (0 : Configuration 1) ∉ tsupport u ∧
      (g : Configuration 1 → ℂ) =ᵐ[volume] u ∧
      (∀ k, (dg k : Configuration 1 → ℂ) =ᵐ[volume] smoothPartial u k) ∧
      (∀ k, WeakPartial g (dg k) k) ∧ HasH2 g ∧
      ‖g-f‖ < ε ∧ ∀ k, ‖dg k-d k‖ < ε := by
  obtain ⟨u,g,dg,hu,huc,hgu,hdu,hdg,hH2,hgf,hdd⟩ :=
    weakH1_smooth_compact_graph_approximation d hd (half_pos hε)
  have hv : ∀ᶠ n in atTop, ‖puncturedAt n g - g‖ < ε / 2 := by
    simpa only [dist_eq_norm] using
      Metric.tendsto_nhds.1 (puncturedAt_tendsto g) (ε / 2) (half_pos hε)
  have hdv : ∀ᶠ n in atTop, ∀ k : Coordinate 1,
      ‖puncturedDerivativeAt n g (dg k) k - dg k‖ < ε / 2 := by
    apply eventually_all.2
    intro k
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.1
      (puncturedDerivativeAt_tendsto g dg hdg k) (ε / 2) (half_pos hε)
  obtain ⟨n, hn, hdn⟩ := (hv.and hdv).exists
  have hgph := puncturedSmooth_actual_graph hu huc g hgu dg hdg n
  refine ⟨puncturedSmooth n u, puncturedAt n g,
    fun k => puncturedDerivativeAt n g (dg k) k,
    puncturedSmooth_contDiff hu n, puncturedSmooth_hasCompactSupport huc n,
    puncturedSmooth_zero_not_mem_tsupport n u, puncturedAt_ae n g hgu,
    hgph.2, fun k => puncturedAt_weakPartial (hdg k) n, hgph.1, ?_, ?_⟩
  · calc ‖puncturedAt n g - f‖ ≤ ‖puncturedAt n g - g‖ + ‖g - f‖ := by
          simpa only [dist_eq_norm] using dist_triangle (puncturedAt n g) g f
         _ < ε := by linarith
  · intro k
    calc ‖puncturedDerivativeAt n g (dg k) k - d k‖ ≤
          ‖puncturedDerivativeAt n g (dg k) k - dg k‖ + ‖dg k - d k‖ := by
          simpa only [dist_eq_norm] using
            dist_triangle (puncturedDerivativeAt n g (dg k) k) (dg k) (d k)
         _ < ε := by linarith [hdn k, hdd k]

set_option pp.proofs false in
#print weakH1_punctured_smooth_compact_graph_approximation
#print axioms weakH1_punctured_smooth_compact_graph_approximation
end TheoremT.Continuum
