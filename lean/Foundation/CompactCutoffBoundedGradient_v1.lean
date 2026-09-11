import CompactCutoffWeakJet_v1
import CompactLocalMultiplierLp_v1
import ScaledCutoffInteriorSupport_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum

theorem cutoff_globally_bounded_weak_gradient {N : ℕ} {A : ℝ} (hA : 0 < A)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hf : MemLp f ⊤ (volume.restrict (Metric.ball 0 (4*A))))
    (hdt : ∀ k, MemLp (d k) ⊤ (volume.restrict (Metric.ball 0 (4*A)))) :
    ∃ u : SpatialL2 N, ∃ a : Coordinate N → SpatialL2 N,
      (∀ k, WeakPartial u (a k) k) ∧ (∀ k, MemLp (a k) ⊤ volume) ∧
      (u : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.ball 0 A)] f := by
  let χ := scaledCutoff N A
  have hc : HasCompactSupport χ := scaledCutoff_hasCompactSupport N hA
  have hχ : ContDiff ℝ ∞ χ := scaledCutoff_contDiff N A
  have hs : tsupport χ ⊆ Metric.ball 0 (4*A) := scaledCutoff_tsupport_subset_four_ball hA
  obtain ⟨u,a,b,hua,hab,hu,ha,hb⟩ := compact_cutoff_weak_jet hχ hc hd he
  refine ⟨u,a,hua,?_,?_⟩
  · intro k
    have hD : Continuous (fun x => fderiv ℝ χ x (coordinateVector k)) :=
      ((hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
    have hsD : Function.support (fun x => fderiv ℝ χ x (coordinateVector k)) ⊆ Metric.ball 0 (4*A) :=
      (subset_tsupport _).trans ((tsupport_fderiv_apply_subset _ _).trans hs)
    have h₁ := compact_multiplier_memLp_of_local Metric.isOpen_ball.measurableSet
      (hχ.continuous.memLp_top_of_hasCompactSupport hc volume) ((subset_tsupport χ).trans hs) (hdt k)
    have h₂ := compact_multiplier_memLp_of_local Metric.isOpen_ball.measurableSet
      (hD.memLp_top_of_hasCompactSupport (hc.fderiv_apply ℝ (coordinateVector k)) volume) hsD hf
    exact MemLp.ae_eq (ha k).symm (h₁.add h₂)
  · filter_upwards [hu.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxa
    change u x = f x
    rw [hx]
    have h1 : χ x=1 := scaledCutoff_eq_one hA (mem_ball_zero_iff.mp hxa).le
    rw [h1,one_smul]

#print axioms cutoff_globally_bounded_weak_gradient
end TheoremT.Continuum
