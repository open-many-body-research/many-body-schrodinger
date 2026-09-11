import CompactCutoffLaplacian_v1
import CompactCutoffLaplacianLp_v1
import ScaledCutoffInteriorSupport_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal
namespace TheoremT.Continuum

theorem interior_poisson_cutoff {N : ℕ} {A : ℝ} (hA : 0 < A) {q : ℝ≥0∞}
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hfq : MemLp f q (volume.restrict (Metric.ball 0 (4*A))))
    (hdq : ∀ k, MemLp (d k) q (volume.restrict (Metric.ball 0 (4*A))))
    (hLq : MemLp (fun x => ∑ k, e k k x) q (volume.restrict (Metric.ball 0 (4*A)))) :
    ∃ u : SpatialL2 N, ∃ a : Coordinate N → SpatialL2 N,
      ∃ b : Coordinate N → Coordinate N → SpatialL2 N,
        (∀ k, WeakPartial u (a k) k) ∧ (∀ k l, WeakPartial (a k) (b k l) l) ∧
        (∀ᵐ x ∂volume, 2*A < ‖x‖ → u x=0) ∧
        MemLp (∑ k : Coordinate N, b k k : SpatialL2 N) q volume ∧
        ∀ k, (a k : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.ball 0 A)] d k := by
  let χ := scaledCutoff N A
  have hχ : ContDiff ℝ ∞ χ := scaledCutoff_contDiff N A
  have hc : HasCompactSupport χ := scaledCutoff_hasCompactSupport N hA
  obtain ⟨u,a,b,hua,hab,hu,ha,hL⟩ := compact_cutoff_weak_laplacian hχ hc hd he
  refine ⟨u,a,b,hua,hab,?_,?_,?_⟩
  · filter_upwards [hu] with x hx
    intro hn
    rw [hx]
    dsimp [χ]
    simp only [scaledCutoff_eq_zero_of_two_mul_le hA hn.le,Complex.ofReal_zero,zero_mul]
  · apply MemLp.ae_eq hL.symm
    exact compact_cutoff_laplacian_rhs_memLp Metric.isOpen_ball.measurableSet hχ hc
      (scaledCutoff_tsupport_subset_four_ball hA) hfq hLq hdq
  · intro k
    filter_upwards [ae_restrict_of_ae (ha k), ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxm
    rw [hx]
    dsimp [χ]
    simp only [scaledCutoff_eq_one hA (mem_ball_zero_iff.mp hxm).le,
      scaledCutoff_fderiv_zero_on_inner_ball hA hxm,ContinuousLinearMap.zero_apply,
      Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,add_zero]

#print axioms interior_poisson_cutoff
end TheoremT.Continuum
