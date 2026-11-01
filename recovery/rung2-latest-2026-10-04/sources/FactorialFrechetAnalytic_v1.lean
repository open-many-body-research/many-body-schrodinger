import FactorialFrechetTaylorConvergence_v1

/-! Actual smoothness plus actual factorial Frechet operator norm bounds
implies a convergent derivative power series. A common interior margin gives
the explicit common radius min(delta, 1/A). No weak-to-smooth bridge is assumed
to have been proved by this generic analytic lemma. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators NNReal ENNReal ContDiff
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem factorial_frechet_hasFPowerSeriesOnBall (f : E → F)
    {Ω : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 < A)
    (hbound : ∀ z ∈ Ω, ∀ k, ‖iteratedFDeriv ℝ k f z‖ ≤ C*A^k*(k.factorial : ℝ))
    (x : E) (r : ℝ≥0) (hr : 0 < r) (hAr : A*(r : ℝ) ≤ 1)
    (hball : Metric.ball x (r : ℝ) ⊆ Ω) :
    HasFPowerSeriesOnBall f (factorialFrechetSeries f x) x (r : ℝ≥0∞) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hxΩ : x ∈ Ω := hball (Metric.mem_ball_self hr')
  refine ⟨factorialFrechetSeries_radius_ge f x r hC hA.le hAr (hbound x hxΩ),
    (by exact_mod_cast hr),?_⟩
  intro y hy
  have hynorm : ‖y‖ < (r : ℝ) := by
    simpa only [Metric.eball_coe,Metric.mem_ball,dist_zero_right] using hy
  have hq : A*‖y‖ < 1 := (mul_lt_mul_of_pos_left hynorm hA).trans_le hAr
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x+t • y ∈ Ω := by
    intro t ht
    apply hball
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg y) ht.2).trans_lt hynorm
  exact factorial_frechet_hasSum_on_segment f x y hC hA.le hq
    (fun t ht => hf.contDiffAt (hΩ.mem_nhds (hseg t ht)))
    (fun t ht => hbound _ (hseg t ht))

theorem factorial_frechet_common_radius (f : E → F)
    {Ω K : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    {C A δ : ℝ} (hC : 0 ≤ C) (hA : 0 < A) (hδ : 0 < δ)
    (hbound : ∀ z ∈ Ω, ∀ k, ‖iteratedFDeriv ℝ k f z‖ ≤ C*A^k*(k.factorial : ℝ))
    (hroom : ∀ x ∈ K, Metric.ball x δ ⊆ Ω) :
    ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ) = min δ A⁻¹ ∧
      ∀ x ∈ K, HasFPowerSeriesOnBall f (factorialFrechetSeries f x) x (r : ℝ≥0∞) := by
  have hp : 0 < min δ A⁻¹ := lt_min hδ (inv_pos.mpr hA)
  let r : ℝ≥0 := ⟨min δ A⁻¹,hp.le⟩
  have hr : 0 < r := by exact_mod_cast hp
  refine ⟨r,hr,rfl,?_⟩
  intro x hx
  apply factorial_frechet_hasFPowerSeriesOnBall f hΩ hf hC hA hbound x r hr
  · calc
      A*(r : ℝ) ≤ A*A⁻¹ := mul_le_mul_of_nonneg_left (min_le_right δ A⁻¹) hA.le
      _ = 1 := mul_inv_cancel₀ hA.ne'
  · exact (Metric.ball_subset_ball (min_le_left δ A⁻¹)).trans (hroom x hx)

theorem factorial_frechet_analyticOnNhd (f : E → F)
    {Ω : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 < A)
    (hbound : ∀ z ∈ Ω, ∀ k, ‖iteratedFDeriv ℝ k f z‖ ≤ C*A^k*(k.factorial : ℝ)) :
    AnalyticOnNhd ℝ f Ω := by
  intro x hx
  obtain ⟨δ,hδ,hroom⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨r,hr,_,hseries⟩ := factorial_frechet_common_radius f
    (K := {x}) hΩ hf hC hA hδ hbound (fun z hz => by simpa only [Set.mem_singleton_iff.mp hz] using hroom)
  exact (hseries x (Set.mem_singleton x)).analyticAt

#print axioms factorial_frechet_hasFPowerSeriesOnBall
#print axioms factorial_frechet_common_radius
#print axioms factorial_frechet_analyticOnNhd
end TheoremT.Continuum
