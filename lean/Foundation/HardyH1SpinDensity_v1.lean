import HardyH1ScalarDensity_v1

/-! Density of actual componentwise weak H² in the full finite-spin weak H¹
graph topology. Fermionic projection is a separate subsequent step. Selection
of the sequence is noncomputable and is not an algorithmic assertion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem spin_h1_approx_by_h2_sequence {N : ℕ} {ψ : SpinSpace N}
    (d : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k) :
    ∃ ψn : ℕ → SpinSpace N, ∃ dn : ℕ → Coordinate N → SpinSpace N,
      (∀ n σ, HasH2 (ψn n σ)) ∧
      (∀ n σ k, WeakPartial (ψn n σ) (dn n k σ) k) ∧
      Tendsto ψn atTop (𝓝 ψ) ∧
      ∀ k, Tendsto (fun n => dn n k) atTop (𝓝 (d k)) := by
  classical
  have happ (n : ℕ) (σ : SpinConfiguration N) :
      ∃ g : SpatialL2 N, ∃ dg : Coordinate N → SpatialL2 N,
        HasH2 g ∧ (∀ k, WeakPartial g (dg k) k) ∧
        ‖g - ψ σ‖ < 1 / ((n : ℝ) + 1) ∧
        ∀ k, ‖dg k - d k σ‖ < 1 / ((n : ℝ) + 1) := by
    obtain ⟨u,g,dg,_,_,_,_,hdg,hH2,hg,hdd⟩ :=
      weakH1_smooth_compact_graph_approximation (fun k => d k σ) (hd σ)
        (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨g,dg,hH2,hdg,hg,hdd⟩
  choose g dg hH2 hdg hg hdd using happ
  have hgt (σ : SpinConfiguration N) :
      Tendsto (fun n => g n σ) atTop (𝓝 (ψ σ)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    simp only [dist_eq_norm]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hg n σ).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdt (σ : SpinConfiguration N) (k : Coordinate N) :
      Tendsto (fun n => dg n σ k) atTop (𝓝 (d k σ)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    simp only [dist_eq_norm]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hdd n σ k).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let ψn : ℕ → SpinSpace N := fun n => WithLp.toLp 2 (g n)
  let dn : ℕ → Coordinate N → SpinSpace N :=
    fun n k => WithLp.toLp 2 (fun σ => dg n σ k)
  refine ⟨ψn,dn,fun n σ => hH2 n σ,fun n σ k => hdg n σ k,?_,?_⟩
  · change Tendsto (fun n => WithLp.toLp 2 (g n)) atTop
      (𝓝 (WithLp.toLp 2 (fun σ => ψ σ)))
    exact ((PiLp.continuous_toLp 2
      (fun _ : SpinConfiguration N => SpatialL2 N)).tendsto _).comp
        (tendsto_pi_nhds.2 hgt)
  · intro k
    change Tendsto (fun n => WithLp.toLp 2 (fun σ => dg n σ k)) atTop
      (𝓝 (WithLp.toLp 2 (fun σ => d k σ)))
    exact ((PiLp.continuous_toLp 2
      (fun _ : SpinConfiguration N => SpatialL2 N)).tendsto _).comp
        (tendsto_pi_nhds.2 (fun σ => hdt σ k))

set_option pp.proofs false in
#print spin_h1_approx_by_h2_sequence
#print axioms spin_h1_approx_by_h2_sequence

end TheoremT.Continuum
