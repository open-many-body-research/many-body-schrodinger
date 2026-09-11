import AllWeakOrdersSmoothRepresentative_v1
import CoulombAllLocalWeakOrders_v1
import CoulombLocallyLipschitz_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_continuous_rep_smooth_away {N : ℕ} {Z E : ℝ}
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {x : Configuration N} (hx : collisionFree x) : ContDiffAt ℝ ∞ g x := by
  obtain ⟨r,hr,χ,hχ,hc,hs,h1⟩ := collisionFree_exists_smooth_cutoff hx
  let u := cutoffMul χ hχ.continuous hc f
  let v : Configuration N → ℂ := fun y => χ y • g y
  have hv : Continuous v := hχ.continuous.smul hg
  have hvc : HasCompactSupport v := hc.smul_right
  have huv : (u : Configuration N → ℂ) =ᵐ[volume] v := by
    filter_upwards [cutoffMul_ae χ hχ.continuous hc f,hfg] with y hy hfgy
    simpa only [v,hfgy] using hy
  have hu (n : ℕ) : HasWeakOrder u n :=
    scalar_coulomb_all_local_weakOrders hgraph n χ hχ hc hs
  have hvd := continuous_integrable_rep_contDiff_of_all_weak_orders u hu hv
    (hv.integrable_of_hasCompactSupport hvc) huv
  apply hvd.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  simp only [v,h1 y hy,one_smul]

theorem scalar_coulomb_locally_lipschitz_smooth_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃ g : Configuration N → ℂ, LocallyLipschitz g ∧
      ((f : Configuration N → ℂ) =ᵐ[volume] g) ∧
      ∀ x, collisionFree x → ContDiffAt ℝ ∞ g x := by
  obtain ⟨g,hg,hfg⟩ := scalar_coulomb_locally_lipschitz_representative hN hgraph
  exact ⟨g,hg,hfg,fun x hx => scalar_coulomb_continuous_rep_smooth_away hgraph hg.continuous hfg hx⟩

#print axioms scalar_coulomb_continuous_rep_smooth_away
#print axioms scalar_coulomb_locally_lipschitz_smooth_representative
end TheoremT.Continuum
