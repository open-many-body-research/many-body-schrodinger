import WeakH2NewtonGradient_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace TheoremT.Continuum

theorem compact_weakH2_poisson_gradient_memLp {N : ℕ} (hN : 0 < N)
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {R : ℝ} (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y=0) (A : ℝ) (k : Coordinate N)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpq : 1/p+1/q=1+1/r)
    (hpd : ((3*N:ℝ)-1)*p < (3*N:ℝ))
    (hL : MemLp (∑ j : Coordinate N, e j j : SpatialL2 N) (ENNReal.ofReal q) volume) :
    MemLp (d k) (ENNReal.ofReal r) (volume.restrict (Metric.closedBall 0 A)) := by
  let K := truncatedNewtonGradient N k (A+(R+2))
  let L : SpatialL2 N := ∑ j : Coordinate N, e j j
  have hKp : MemLp K (ENNReal.ofReal p) volume := truncatedNewtonGradient_memLp hN k _ hp hpd
  have hC := young_bochner_smul_memLp
    (truncatedNewtonGradient_measurable N k _).stronglyMeasurable (Lp.stronglyMeasurable L)
    hp hq hr hpr hqr hpq hKp hL
  apply MemLp.ae_eq (hf_Lp := hC.mono_measure Measure.restrict_le_self)
  have hrp := compact_weakH2_newton_gradient_representation hN d e hd he hs A k
  filter_upwards [ae_restrict_of_ae hrp, ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx hxm
  exact (hx (by simpa only [mem_closedBall_zero_iff] using hxm)).symm

theorem compact_weakH2_poisson_gradient_eLpNorm_le {N : ℕ} (hN : 0 < N)
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {R : ℝ} (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y=0) (A : ℝ) (k : Coordinate N)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpq : 1/p+1/q=1+1/r) :
    eLpNorm (d k) (ENNReal.ofReal r) (volume.restrict (Metric.closedBall 0 A)) ≤
      eLpNorm (truncatedNewtonGradient N k (A+(R+2))) (ENNReal.ofReal p) volume *
        eLpNorm (∑ j : Coordinate N, e j j : SpatialL2 N) (ENNReal.ofReal q) volume := by
  let K := truncatedNewtonGradient N k (A+(R+2))
  let L : SpatialL2 N := ∑ j : Coordinate N, e j j
  have hrp := compact_weakH2_newton_gradient_representation hN d e hd he hs A k
  have hEq : (d k : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.closedBall 0 A)]
      (fun x => ∫ y, K y • L (x-y)) := by
    filter_upwards [ae_restrict_of_ae hrp, ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx hxm
    exact hx (by simpa only [mem_closedBall_zero_iff] using hxm)
  rw [eLpNorm_congr_ae hEq]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    (young_bochner_smul_eLpNorm_le (truncatedNewtonGradient_measurable N k _).stronglyMeasurable
      (Lp.stronglyMeasurable L) hp hq hr hpr hqr hpq)

#print axioms compact_weakH2_poisson_gradient_memLp
#print axioms compact_weakH2_poisson_gradient_eLpNorm_le
end TheoremT.Continuum
