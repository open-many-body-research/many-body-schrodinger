import HardyLaplacianRegularization_v1
import HardyLaplacianL2Core_v1
import HardyMollifierStrongRepresentation_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem mollifyLp_partial_ae {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (m : ℕ) :
    (mollifyLp m g : Configuration N → ℂ) =ᵐ[volume]
      smoothPartial (mollify (mollifierKernel N m) f) k := by
  rw [smoothPartial_mollify hg _ (mollifierKernel_contDiff N m)
    (mollifierKernel_hasCompactSupport N m)]
  exact mollifyLp_ae m g

theorem mollifyLp_laplacian_ae {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (m : ℕ) :
    ((∑ k : Coordinate N, mollifyLp m (e k k) : SpatialL2 N) : Configuration N → ℂ) =ᵐ[volume]
      smoothLaplacian (mollify (mollifierKernel N m) f) := by
  have hae : ∀ᵐ x : Configuration N, ∀ k : Coordinate N,
      mollifyLp m (e k k) x = mollify (mollifierKernel N m) (e k k) x := by
    rw [ae_all_iff]
    intro k
    exact mollifyLp_ae m (e k k)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun k => mollifyLp m (e k k)), hae]
    with x hx hxe
  rw [hx, smoothLaplacian_mollify d e hd he _ (mollifierKernel_contDiff N m)
    (mollifierKernel_hasCompactSupport N m)]
  exact Finset.sum_congr rfl (fun k _ => hxe k)

/-- The exact smooth-core energy identity for the concrete derivative-compatible
mollification, stated using L² norms and the actual weak second derivatives. -/
theorem mollifyLp_compact_energy_identity {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (m : ℕ) (hc : HasCompactSupport (mollify (mollifierKernel N m) f)) :
    (∑ k : Coordinate N, ‖mollifyLp m (d k)‖^2) =
      -inner ℝ (mollifyLp m f) (∑ k : Coordinate N, mollifyLp m (e k k)) := by
  exact compact_energy_identity_L2
    (mollify_contDiff _ (mollifierKernel_contDiff N m) (mollifierKernel_hasCompactSupport N m) f)
    hc (mollifyLp m f) (fun k => mollifyLp m (d k)) _
    (mollifyLp_ae m f) (fun k => mollifyLp_partial_ae (hd k) m)
    (mollifyLp_laplacian_ae d e hd he m)

#print axioms mollifyLp_laplacian_ae
#print axioms mollifyLp_compact_energy_identity
end TheoremT.Continuum
