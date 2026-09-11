import CoulombLocalWeakOrderGain_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_coulomb_all_local_weakOrders {N : ℕ} {Z E : ℝ} {f : SpatialL2 N}
    (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∀ n : ℕ, HasLocalWeakOrder f {x | collisionFree x} n := by
  have hf2 : HasH2 f := by
    obtain ⟨d,e,hd,he,_⟩ := hgraph
    exact ⟨d,hd,fun k l => ⟨e k l,he k l⟩⟩
  have hh (n : ℕ) : HasLocalWeakOrder f {x | collisionFree x} (n+2) := by
    induction n with
    | zero => exact ((hasWeakOrder_two_iff f).mpr hf2).localize _
    | succ n ih =>
      exact scalar_coulomb_local_weakOrder_gain (n := n+1) hgraph ih
  exact fun n => (hh n).mono (Nat.le_add_right n 2)

theorem scalar_coulomb_one_local_all_orders_representative {N : ℕ} {Z E : ℝ} {f : SpatialL2 N}
    (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {x : Configuration N} (hx : collisionFree x) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : SpatialL2 N,
      u =ᵐ[volume.restrict (Metric.ball x r)] f ∧ ∀ n : ℕ, HasWeakOrder u n := by
  obtain ⟨r,hr,χ,hχ,hc,hs,h1⟩ := collisionFree_exists_smooth_cutoff hx
  let u := cutoffMul χ hχ.continuous hc f
  refine ⟨r,hr,u,?_,fun n => scalar_coulomb_all_local_weakOrders hgraph n χ hχ hc hs⟩
  filter_upwards [ae_restrict_of_ae (cutoffMul_ae χ hχ.continuous hc f),
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hyB
  simpa only [h1 y hyB,one_smul] using hy

#print axioms scalar_coulomb_all_local_weakOrders
#print axioms scalar_coulomb_one_local_all_orders_representative
end TheoremT.Continuum
