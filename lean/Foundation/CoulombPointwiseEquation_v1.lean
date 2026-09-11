import CoulombSmoothAway_v1
import CompactSmoothJetIdentification_v1
import KSHoleSupport_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology BigOperators
namespace TheoremT.Continuum

theorem scalar_coulomb_continuous_rep_pointwise_equation {N : ℕ} {Z E : ℝ}
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {x : Configuration N} (hx : collisionFree x) :
    smoothLaplacian g x=2*((coulombPotential N Z x : ℂ)-(E:ℂ))*g x := by
  obtain ⟨r,hr,χ,hχ,hc,hs,h1⟩ := collisionFree_exists_smooth_cutoff hx
  let v : Configuration N → ℂ := fun y => χ y • g y
  have hv : Continuous v := hχ.continuous.smul hg
  have hvc : HasCompactSupport v := hc.smul_right
  let w := cutoffMul χ hχ.continuous hc f
  have hwv : (w : Configuration N → ℂ) =ᵐ[volume] v := by
    filter_upwards [cutoffMul_ae χ hχ.continuous hc f,hfg] with y hy hfgy
    simpa only [v,hfgy] using hy
  have hwo (n : ℕ) : HasWeakOrder w n :=
    scalar_coulomb_all_local_weakOrders hgraph n χ hχ hc hs
  have hvd := continuous_integrable_rep_contDiff_of_all_weak_orders w hwo hv
    (hv.integrable_of_hasCompactSupport hvc) hwv
  obtain ⟨d,e,hd,he,hge⟩ := hgraph
  obtain ⟨u,a,b,hua,hab,hu,ha,hb⟩ := compact_cutoff_weak_laplacian hχ hc hd he
  have huv : (u : Configuration N → ℂ) =ᵐ[volume] v := by
    filter_upwards [hu,hfg] with y hy hfgy
    simpa only [v,hfgy] using hy
  have hL := weakH2_laplacian_ae_smooth_of_compact_rep a b hua hab hvd hvc huv
  have hzero {y : Configuration N} (hy : y ∈ Metric.ball x r) (k l : Coordinate N) :
      fderiv ℝ χ y (coordinateVector k)=0 ∧
      fderiv ℝ (fun z => fderiv ℝ χ z (coordinateVector k)) y (coordinateVector l)=0 := by
    apply locally_constant_first_second_zero (c := 1)
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact h1 z hz
  have hAE : smoothLaplacian v =ᵐ[volume.restrict (Metric.ball x r)]
      (fun y => 2*((coulombPotential N Z y : ℂ)-(E:ℂ))*g y) := by
    filter_upwards [ae_restrict_of_ae hL,ae_restrict_of_ae hb,ae_restrict_of_ae hge,
      ae_restrict_of_ae (Lp.coeFn_smul (E:ℂ) f),ae_restrict_of_ae hfg,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hLy hby hgey hEy hfgy hy
    have hzL : realTestLaplacian χ y=0 := by
      simp only [realTestLaplacian,(hzero hy _ _).2,Finset.sum_const_zero]
    rw [hEy] at hgey
    change (E:ℂ)*f y=_ at hgey
    have hΔ : (∑ k,e k k y)=2*((coulombPotential N Z y : ℂ)-(E:ℂ))*f y := by
      linear_combination 2*hgey
    have hzD (k : Coordinate N) : fderiv ℝ χ y (coordinateVector k)=0 := (hzero hy k k).1
    rw [hLy,h1 y hy] at hby
    simpa only [hzD,hzL,Complex.ofReal_one,Complex.ofReal_zero,
      zero_mul,Finset.sum_const_zero,mul_zero,add_zero,one_mul,hΔ,hfgy] using hby
  have hvL : Continuous (smoothLaplacian v) := by
    apply continuous_finset_sum
    intro k _
    exact (smoothPartial_contDiff (smoothPartial_contDiff hvd k) k).continuous
  have hR : ContinuousOn (fun y : Configuration N =>
      2*((coulombPotential N Z y : ℂ)-(E:ℂ))*g y) (Metric.ball x r) := by
    intro y hy
    have hyc : collisionFree y := hs y (subset_tsupport χ (by simp [Function.mem_support,h1 y hy]))
    have hVy : ContinuousAt (fun z => (coulombPotential N Z z : ℂ)) y :=
      Complex.continuous_ofReal.continuousAt.comp (coulombPotential_contDiffAt_collisionFree Z hyc).continuousAt
    exact ((continuousAt_const.mul (hVy.sub continuousAt_const)).mul hg.continuousAt).continuousWithinAt
  have hpt := volume.eqOn_open_of_ae_eq hAE Metric.isOpen_ball hvL.continuousOn hR
    (Metric.mem_ball_self hr)
  have heq : v =ᶠ[𝓝 x] g := by
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    simp only [v,h1 y hy,one_smul]
  rwa [smoothLaplacian_congr_of_eventuallyEq heq] at hpt

theorem scalar_coulomb_classical_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃ g : Configuration N → ℂ, LocallyLipschitz g ∧
      ((f : Configuration N → ℂ) =ᵐ[volume] g) ∧
      ∀ x, collisionFree x → ContDiffAt ℝ ∞ g x ∧
        smoothLaplacian g x=2*((coulombPotential N Z x : ℂ)-(E:ℂ))*g x := by
  obtain ⟨g,hg,hfg,hgs⟩ := scalar_coulomb_locally_lipschitz_smooth_representative hN hgraph
  exact ⟨g,hg,hfg,fun x hx => ⟨hgs x hx,
    scalar_coulomb_continuous_rep_pointwise_equation hgraph hg.continuous hfg hx⟩⟩

#print axioms scalar_coulomb_continuous_rep_pointwise_equation
#print axioms scalar_coulomb_classical_representative
end TheoremT.Continuum
