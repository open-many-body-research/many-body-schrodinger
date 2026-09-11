import HardyWeakIBP_v1
import HardyMollifierStrong_v1

/-! Integration by parts on the original distributional weak domain, with the
mollifier and cutoff convergence obligations discharged by actual constructions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem weakPartial_ibp_of_compact_mollifications {N : ℕ}
    {f g df dg : SpatialL2 N} {k : Coordinate N}
    (hdf : WeakPartial f df k) (hdg : WeakPartial g dg k)
    (hc : ∀ m : ℕ, HasCompactSupport (mollify (mollifierKernel N m) f)) :
    inner ℂ f dg = -inner ℂ df g := by
  have hh : (fun m : ℕ => inner ℂ (mollifyLp m f) (mollifyLp m dg)) =
      (fun m : ℕ => -inner ℂ (mollifyLp m df) (mollifyLp m g)) := by
    funext m
    exact mollifyLp_compact_ibp hdf hdg m (hc m)
  have hl := (mollifyLp_tendsto f).inner (𝕜 := ℂ) (mollifyLp_tendsto dg)
  have hr := ((mollifyLp_tendsto df).inner (𝕜 := ℂ) (mollifyLp_tendsto g)).neg
  rw [hh] at hl
  exact tendsto_nhds_unique hl hr

/-- Actual complex integration by parts for two weak partial derivatives. No
smoothness, core-density, compact-support, or approximation hypothesis remains. -/
theorem weakPartial_complex_ibp {N : ℕ} {f g df dg : SpatialL2 N} {k : Coordinate N}
    (hdf : WeakPartial f df k) (hdg : WeakPartial g dg k) :
    inner ℂ f dg = -inner ℂ df g := by
  have hh : (fun n : ℕ => inner ℂ (cutoffAt n f) (cutoffDerivativeAt n g dg k)) =
      (fun n : ℕ => -inner ℂ (cutoffDerivativeAt n f df k) (cutoffAt n g)) := by
    funext n
    exact weakPartial_ibp_of_compact_mollifications
      (cutoffDerivativeAt_weakPartial hdf n) (cutoffDerivativeAt_weakPartial hdg n)
      (fun m => (mollifyKernel_cutoff_contDiff_compact n m f).2)
  have hl := (cutoffAt_tendsto f).inner (𝕜 := ℂ) (cutoffDerivativeAt_tendsto g dg k)
  have hr := ((cutoffDerivativeAt_tendsto f df k).inner (𝕜 := ℂ) (cutoffAt_tendsto g)).neg
  rw [hh] at hl
  exact tendsto_nhds_unique hl hr

#print axioms weakPartial_complex_ibp
end TheoremT.Continuum
