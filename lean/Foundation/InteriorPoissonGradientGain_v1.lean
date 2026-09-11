import InteriorPoissonCutoff_v1
import WeakH2PoissonLpGain_v1
import WeakH2PoissonBoundedGradient_v1

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem interior_weakH2_poisson_gradient_memLp {N : ℕ} (hN : 0 < N) {A : ℝ} (hA : 0 < A)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpq : 1/p+1/q=1+1/r)
    (hpd : ((3*N:ℝ)-1)*p < (3*N:ℝ))
    (hfq : MemLp f (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (4*A))))
    (hdq : ∀ k, MemLp (d k) (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (4*A))))
    (hLq : MemLp (fun x => ∑ k, e k k x) (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (4*A)))) :
    ∀ k, MemLp (d k) (ENNReal.ofReal r) (volume.restrict (Metric.ball 0 A)) := by
  obtain ⟨u,a,b,hua,hab,hs,hL,ha⟩ := interior_poisson_cutoff hA hd he hfq hdq hLq
  intro k
  have hk := compact_weakH2_poisson_gradient_memLp hN a b hua hab hs A k hp hq hr hpr hqr hpq hpd hL
  exact MemLp.ae_eq (ha k) (hk.mono_measure (Measure.restrict_mono_set volume Metric.ball_subset_closedBall))

theorem interior_weakH2_poisson_gradient_memLp_top {N : ℕ} (hN : 0 < N) {A : ℝ} (hA : 0 < A)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpd : ((3*N:ℝ)-1)*p < (3*N:ℝ))
    (hfq : MemLp f (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (4*A))))
    (hdq : ∀ k, MemLp (d k) (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (4*A))))
    (hLq : MemLp (fun x => ∑ k, e k k x) (ENNReal.ofReal q) (volume.restrict (Metric.ball 0 (4*A)))) :
    ∀ k, MemLp (d k) ⊤ (volume.restrict (Metric.ball 0 A)) := by
  obtain ⟨u,a,b,hua,hab,hs,hL,ha⟩ := interior_poisson_cutoff hA hd he hfq hdq hLq
  intro k
  have hk := compact_weakH2_poisson_gradient_memLp_top hN a b hua hab hs A k hpq hpd hL
  exact MemLp.ae_eq (ha k) (hk.mono_measure (Measure.restrict_mono_set volume Metric.ball_subset_closedBall))

#print axioms interior_weakH2_poisson_gradient_memLp
#print axioms interior_weakH2_poisson_gradient_memLp_top
end TheoremT.Continuum
