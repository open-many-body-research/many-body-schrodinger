import PuncturedH1Density_v1

/-! Sequential density of the punctured smooth compact core in actual one-electron H¹.
This is a noncomputable mathematical sequence, not an executable approximation algorithm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem weakH1_punctured_smooth_compact_graph_sequence {f : SpatialL2 1}
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k) :
    ∃ u : ℕ → Configuration 1 → ℂ, ∃ g : ℕ → SpatialL2 1,
      ∃ dg : ℕ → Coordinate 1 → SpatialL2 1,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, (0 : Configuration 1) ∉ tsupport (u n)) ∧
      (∀ n, (g n : Configuration 1 → ℂ) =ᵐ[volume] u n) ∧
      (∀ n k, (dg n k : Configuration 1 → ℂ) =ᵐ[volume] smoothPartial (u n) k) ∧
      (∀ n k, WeakPartial (g n) (dg n k) k) ∧ (∀ n, HasH2 (g n)) ∧
      Tendsto g atTop (𝓝 f) ∧
      ∀ k, Tendsto (fun n => dg n k) atTop (𝓝 (d k)) := by
  classical
  have happ (n : ℕ) := weakH1_punctured_smooth_compact_graph_approximation d hd
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose u g dg hu hc hzero hgu hdgu hdg hH2 hg hdd using happ
  refine ⟨u,g,dg,hu,hc,hzero,hgu,hdgu,hdg,hH2,?_,?_⟩
  · apply tendsto_iff_dist_tendsto_zero.2
    simp only [dist_eq_norm]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hg n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro k
    apply tendsto_iff_dist_tendsto_zero.2
    simp only [dist_eq_norm]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hdd n k).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

set_option pp.proofs false in
#print weakH1_punctured_smooth_compact_graph_sequence
#print axioms weakH1_punctured_smooth_compact_graph_sequence
end TheoremT.Continuum
