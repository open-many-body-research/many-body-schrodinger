import GenericMollifierSequence_v1

/-!
A single explicitly specified mollifier sequence approximates every component
of an actual compact weak H2 jet on any finite-dimensional Euclidean space.
One closed ball contains the support of every smooth approximant. The weak
hypotheses are the actual compact-test integration-by-parts identities, and
all convergence is in the actual Lebesgue L2 quotient space.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum.GenericMollifier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem mollifierKernel_eq_zero_of_two_lt_norm {n : ℕ} {x : E}
    (hx : 2 < ‖x‖) : mollifierKernel n x = 0 := by
  have hr : (mollifierBump (E := E) n).rOut ≤ 2 := by
    dsimp [mollifierBump]
    have h : ((n:ℝ)+1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hn : x ∉ Function.support (mollifierKernel n) := by
    rw [mollifierKernel,(mollifierBump (E := E) n).support_normed_eq]
    simpa only [mem_ball_zero_iff,not_lt] using (hr.trans hx.le)
  simpa only [Function.mem_support,not_not] using hn

theorem mollify_eq_zero_outside_of_ae_support {R : ℝ}
    {f : Lp ℂ 2 (volume : Measure E)}
    (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y = 0) (n : ℕ) {x : E}
    (hx : R+2 < ‖x‖) : mollify (mollifierKernel n) f x = 0 := by
  unfold mollify
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with y hy
  by_cases h : R < ‖y‖
  · simp only [hy h,smul_zero,Pi.zero_apply]
  · have hb : 2 < ‖x-y‖ := by
      have he : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa using norm_add_le (x-y) y
      push_neg at h
      linarith
    simp only [mollifierKernel_eq_zero_of_two_lt_norm hb,zero_smul,Pi.zero_apply]

theorem mollify_tsupport_subset_closedBall {R : ℝ}
    {f : Lp ℂ 2 (volume : Measure E)}
    (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y = 0) (n : ℕ) :
    tsupport (mollify (mollifierKernel n) f) ⊆ Metric.closedBall 0 (R+2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  exact hx (mollify_eq_zero_outside_of_ae_support hs n (lt_of_not_ge hn))

theorem mollify_compact_of_ae_support {R : ℝ}
    {f : Lp ℂ 2 (volume : Measure E)}
    (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y = 0) (n : ℕ) :
    HasCompactSupport (mollify (mollifierKernel n) f) :=
  (isCompact_closedBall (0 : E) (R+2)).of_isClosed_subset
    (isClosed_tsupport _) (mollify_tsupport_subset_closedBall hs n)

theorem mollifyLp_directional_ae {f g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hg : WeakL2Directional f g v) (n : ℕ) :
    (mollifyLp n g : E → ℂ) =ᵐ[volume]
      (fun x => fderiv ℝ (mollify (mollifierKernel n) f) x v) := by
  filter_upwards [mollifyLp_ae n g] with x hx
  rw [hx, mollify_derivative hg _ (mollifierKernel_contDiff n)
    (mollifierKernel_hasCompactSupport n)]

theorem mollifyLp_second_directional_ae
    {f g h : Lp ℂ 2 (volume : Measure E)} {v w : E}
    (hg : WeakL2Directional f g v) (hh : WeakL2Directional g h w) (n : ℕ) :
    (mollifyLp n h : E → ℂ) =ᵐ[volume]
      (fun x => fderiv ℝ (fun z => fderiv ℝ (mollify (mollifierKernel n) f) z v) x w) := by
  have hd : (fun z => fderiv ℝ (mollify (mollifierKernel n) f) z v) =
      mollify (mollifierKernel n) g := by
    funext z
    exact mollify_derivative hg _ (mollifierKernel_contDiff n)
      (mollifierKernel_hasCompactSupport n) z
  rw [hd]
  exact mollifyLp_directional_ae hh n

theorem compact_weakH2_uniform_support_approximation
    {f : Lp ℂ 2 (volume : Measure E)}
    (d : E → Lp ℂ 2 (volume : Measure E))
    (e : E → E → Lp ℂ 2 (volume : Measure E))
    (hd : ∀ v, WeakL2Directional f (d v) v)
    (he : ∀ v w, WeakL2Directional (d v) (e v w) w)
    {R : ℝ} (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y = 0) :
    ∃ u : ℕ → E → ℂ, ∃ g : ℕ → Lp ℂ 2 (volume : Measure E),
      ∃ dg : ℕ → E → Lp ℂ 2 (volume : Measure E),
      ∃ eg : ℕ → E → E → Lp ℂ 2 (volume : Measure E),
      (∀ n, ContDiff ℝ ∞ (u n)) ∧
      (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, tsupport (u n) ⊆ Metric.closedBall 0 (R+2)) ∧
      (∀ n, (g n : E → ℂ) =ᵐ[volume] u n) ∧
      (∀ n v, (dg n v : E → ℂ) =ᵐ[volume] (fun x => fderiv ℝ (u n) x v)) ∧
      (∀ n v w, (eg n v w : E → ℂ) =ᵐ[volume]
        (fun x => fderiv ℝ (fun z => fderiv ℝ (u n) z v) x w)) ∧
      Tendsto g atTop (𝓝 f) ∧
      (∀ v, Tendsto (fun n => dg n v) atTop (𝓝 (d v))) ∧
      (∀ v w, Tendsto (fun n => eg n v w) atTop (𝓝 (e v w))) := by
  refine ⟨(fun n => mollify (mollifierKernel n) f), (fun n => mollifyLp n f),
    (fun n v => mollifyLp n (d v)), (fun n v w => mollifyLp n (e v w)),
    (fun n => mollify_contDiff _ (mollifierKernel_contDiff n)
      (mollifierKernel_hasCompactSupport n) f),
    (fun n => mollify_compact_of_ae_support hs n),
    (fun n => mollify_tsupport_subset_closedBall hs n),
    (fun n => mollifyLp_ae n f),
    (fun n v => mollifyLp_directional_ae (hd v) n),
    (fun n v w => mollifyLp_second_directional_ae (hd v) (he v w) n),
    mollifyLp_tendsto f, (fun v => mollifyLp_tendsto (d v)),
    (fun v w => mollifyLp_tendsto (e v w))⟩

end TheoremT.Continuum.GenericMollifier
