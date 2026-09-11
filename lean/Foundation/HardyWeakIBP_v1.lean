import HardyLaplacianRegularization_v2

/-! Complex integration by parts for concrete smoothings of weak-derivative data. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem mollifyLp_compact_ibp {N : ℕ} {f g df dg : SpatialL2 N} {k : Coordinate N}
    (hdf : WeakPartial f df k) (hdg : WeakPartial g dg k)
    (m : ℕ) (hc : HasCompactSupport (mollify (mollifierKernel N m) f)) :
    inner ℂ (mollifyLp m f) (mollifyLp m dg) =
      -inner ℂ (mollifyLp m df) (mollifyLp m g) := by
  exact compact_complex_ibp_L2
    (mollify_contDiff _ (mollifierKernel_contDiff N m) (mollifierKernel_hasCompactSupport N m) f)
    (mollify_contDiff _ (mollifierKernel_contDiff N m) (mollifierKernel_hasCompactSupport N m) g)
    hc _ _ _ _ k (mollifyLp_ae m f) (mollifyLp_ae m g)
    (mollifyLp_partial_ae hdf m) (mollifyLp_partial_ae hdg m)

#print axioms mollifyLp_compact_ibp
end TheoremT.Continuum
