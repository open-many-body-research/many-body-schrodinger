import TruncatedNewtonGradient_v1
import RealKernelConvolutionCongruence_v1
import L2LocalEqualityClosure_v1
import HardySobolevDensity_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem compact_weakH2_newton_gradient_representation {N : ℕ} (hN : 0 < N)
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {R : ℝ} (hs : ∀ᵐ y ∂volume, R < ‖y‖ → f y=0) (A : ℝ) (k : Coordinate N) :
    ∀ᵐ x ∂volume, ‖x‖ ≤ A →
      d k x = ∫ y, truncatedNewtonGradient N k (A+(R+2)) y •
        (∑ j : Coordinate N, e j j : SpatialL2 N) (x-y) := by
  let K := truncatedNewtonGradient N k (A+(R+2))
  have hKm : StronglyMeasurable K := (truncatedNewtonGradient_measurable N k _).stronglyMeasurable
  have hKi : Integrable K := truncatedNewtonGradient_integrable hN k _
  let Lm (m : ℕ) : SpatialL2 N := ∑ j : Coordinate N, mollifyLp m (e j j)
  let L : SpatialL2 N := ∑ j : Coordinate N, e j j
  have hLm : Tendsto Lm atTop (𝓝 L) :=
    tendsto_finset_sum Finset.univ (fun j hj => mollifyLp_tendsto (e j j))
  have hC := (realKernelConvolutionL2_continuous K hKm hKi).tendsto L
  have hseq : ∀ m, ∀ᵐ x ∂volume, x ∈ {x : Configuration N | ‖x‖ ≤ A} →
      realKernelConvolutionL2 K hKm hKi (Lm m) x=mollifyLp m (d k) x := by
    intro m
    have hl : (Lm m : Configuration N → ℂ) =ᵐ[volume]
        smoothLaplacian (mollify (mollifierKernel N m) f) := mollifyLp_laplacian_ae d e hd he m
    have hu : ContDiff ℝ ∞ (mollify (mollifierKernel N m) f) :=
      mollify_contDiff _ (mollifierKernel_contDiff N m) (mollifierKernel_hasCompactSupport N m) f
    filter_upwards [realKernelConvolutionL2_ae_representative K hKm hKi (Lm m) hl,
      mollifyLp_partial_ae (hd k) m] with x hcx hdx
    intro hx
    rw [hcx,hdx]
    exact truncated_newton_gradient_smooth_representation hN hu
      (mollify_tsupport_subset_closedBall hs m) x hx k
  have hlim := l2_local_equality_closed (hC.comp hLm) (mollifyLp_tendsto (d k)) hseq
  filter_upwards [hlim,realKernelConvolutionL2_ae K hKm hKi L] with x hx hCx
  intro hxA
  exact (hx hxA).symm.trans hCx

#print axioms compact_weakH2_newton_gradient_representation
end TheoremT.Continuum
