import MollifierSequence_v2
import HardyWeakConvolution_v3
import HardyWeakTransfer_v2

/-! Actual L² representatives of the normalized shrinking mollifiers. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem mollifier_memLp {N : ℕ} (n : ℕ) (f : SpatialL2 N) :
    MemLp (mollify (mollifierKernel N n) f) 2 volume :=
  (mollify_memLp_two_and_bound _ (mollifierKernel_contDiff N n).continuous.measurable
    (mollifierKernel_nonneg N n) (mollifierKernel_integrable N n)
    (mollifierKernel_integral N n) f).1

def mollifyLp {N : ℕ} (n : ℕ) (f : SpatialL2 N) : SpatialL2 N :=
  (mollifier_memLp n f).toLp (mollify (mollifierKernel N n) f)

theorem mollifyLp_ae {N : ℕ} (n : ℕ) (f : SpatialL2 N) :
    mollifyLp n f =ᵐ[volume] mollify (mollifierKernel N n) f :=
  (mollifier_memLp n f).coeFn_toLp

theorem mollifyLp_norm_le {N : ℕ} (n : ℕ) (f : SpatialL2 N) :
    ‖mollifyLp n f‖ ≤ ‖f‖ := by
  have he : ‖mollifyLp n f‖^2 = ∫ x, ‖mollify (mollifierKernel N n) f x‖^2 := by
    rw [spatialL2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [mollifyLp_ae n f] with x hx
    rw [hx]
  have hb := (mollify_memLp_two_and_bound _
    (mollifierKernel_contDiff N n).continuous.measurable (mollifierKernel_nonneg N n)
    (mollifierKernel_integrable N n) (mollifierKernel_integral N n) f).2
  rw [← he, ← spatialL2_norm_sq_eq_integral] at hb
  nlinarith [norm_nonneg (mollifyLp n f), norm_nonneg f]

theorem mollifyLp_ae_tendsto {N : ℕ} (f : SpatialL2 N) :
    ∀ᵐ x ∂volume, Tendsto (fun n : ℕ => mollifyLp n f x) atTop (𝓝 (f x)) := by
  have ha : ∀ᵐ x ∂volume, ∀ n : ℕ, mollifyLp n f x = mollify (mollifierKernel N n) f x := by
    rw [ae_all_iff]
    intro n
    exact mollifyLp_ae n f
  filter_upwards [ha, mollifyKernel_ae_tendsto f] with x hx hlim
  simpa only [hx] using hlim

#print axioms mollifyLp_ae
#print axioms mollifyLp_norm_le
#print axioms mollifyLp_ae_tendsto
end TheoremT.Continuum
