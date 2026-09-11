import WeakH2NewtonGradient_v1
import HolderBochnerConvolution_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace TheoremT.Continuum

theorem compact_weakH2_poisson_gradient_memLp_top {N : ℕ} (hN : 0 < N)
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {R : ℝ} (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y=0) (A : ℝ) (k : Coordinate N)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hpd : ((3*N:ℝ)-1)*p < (3*N:ℝ))
    (hL : MemLp (∑ j : Coordinate N, e j j : SpatialL2 N) (ENNReal.ofReal q) volume) :
    MemLp (d k) ⊤ (volume.restrict (Metric.closedBall 0 A)) := by
  let K := truncatedNewtonGradient N k (A+(R+2))
  let L : SpatialL2 N := ∑ j : Coordinate N, e j j
  have hKp : MemLp K (ENNReal.ofReal p) volume := truncatedNewtonGradient_memLp hN k _ hpq.pos hpd
  have hC := holder_bochner_smul_memLp_top
    (truncatedNewtonGradient_measurable N k _).stronglyMeasurable (Lp.stronglyMeasurable L)
    hpq hKp hL
  apply MemLp.ae_eq (hf_Lp := hC.mono_measure Measure.restrict_le_self)
  have hrp := compact_weakH2_newton_gradient_representation hN d e hd he hs A k
  filter_upwards [ae_restrict_of_ae hrp, ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx hxm
  exact (hx (by simpa only [mem_closedBall_zero_iff] using hxm)).symm

#print axioms compact_weakH2_poisson_gradient_memLp_top
end TheoremT.Continuum
