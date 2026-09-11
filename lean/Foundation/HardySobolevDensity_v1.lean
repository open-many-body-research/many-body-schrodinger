import HardyMollifierStrong_v1
import HardyLaplacianRegularization_v2
import HardyWeakCore_v1

/-! Mollification preserves the actual weak derivative graph, with its existing
L² representatives, rather than introducing a separate Sobolev definition. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem mollifyLp_weakPartial {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (m : ℕ) :
    WeakPartial (mollifyLp m f) (mollifyLp m g) k := by
  let u := mollify (mollifierKernel N m) f
  have hu : ContDiff ℝ ∞ u := mollify_contDiff _
    (mollifierKernel_contDiff N m) (mollifierKernel_hasCompactSupport N m) f
  have heq : (fun x => fderiv ℝ u x (coordinateVector k)) =
      mollify (mollifierKernel N m) g :=
    smoothPartial_mollify hg _ (mollifierKernel_contDiff N m)
      (mollifierKernel_hasCompactSupport N m)
  have hd : MemLp (fun x => fderiv ℝ u x (coordinateVector k)) 2 volume := by
    rw [heq]
    exact mollifier_memLp m g
  have hdeq : hd.toLp (fun x => fderiv ℝ u x (coordinateVector k)) = mollifyLp m g := by
    apply Lp.ext
    exact hd.coeFn_toLp.trans ((Filter.EventuallyEq.of_eq heq).trans (mollifyLp_ae m g).symm)
  have hh := classicalDerivative_to_WeakPartial (hu.of_le (by simp)) k
    (mollifier_memLp m f) hd
  change WeakPartial (mollifyLp m f) _ k at hh
  rwa [hdeq] at hh

theorem mollifyLp_second_ae {N : ℕ} {f dk e : SpatialL2 N} {k l : Coordinate N}
    (hd : WeakPartial f dk k) (he : WeakPartial dk e l) (m : ℕ) :
    (mollifyLp m e : Configuration N → ℂ) =ᵐ[volume]
      smoothPartial (smoothPartial (mollify (mollifierKernel N m) f) k) l := by
  rw [smoothSecond_mollify hd he _ (mollifierKernel_contDiff N m)
    (mollifierKernel_hasCompactSupport N m)]
  exact mollifyLp_ae m e

#print axioms mollifyLp_weakPartial
#print axioms mollifyLp_second_ae
end TheoremT.Continuum
