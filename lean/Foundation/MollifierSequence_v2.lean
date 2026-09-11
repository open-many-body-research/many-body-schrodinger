import ScaledCutoff_v2
import HardyWeakConvolution_v1
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-! A concrete normalized smooth approximate identity and its almost-everywhere
convergence for the actual configuration-space L2 representatives. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Convolution
namespace TheoremT.Continuum

def mollifierBump (N n : ℕ) : ContDiffBump (0 : Configuration N) where
  rIn := ((n : ℝ) + 1)⁻¹
  rOut := 2 * ((n : ℝ) + 1)⁻¹
  rIn_pos := inv_pos.mpr (by positivity)
  rIn_lt_rOut := by
    have h : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
    linarith

def mollifierKernel (N n : ℕ) : Configuration N → ℝ :=
  (mollifierBump N n).normed volume

theorem mollifierKernel_nonneg (N n : ℕ) (x : Configuration N) :
    0 ≤ mollifierKernel N n x := (mollifierBump N n).nonneg_normed x

theorem mollifierKernel_integral (N n : ℕ) :
    (∫ x, mollifierKernel N n x) = 1 := (mollifierBump N n).integral_normed

theorem mollifierKernel_integrable (N n : ℕ) :
    Integrable (mollifierKernel N n) := (mollifierBump N n).integrable_normed

theorem mollifierKernel_contDiff (N n : ℕ) :
    ContDiff ℝ ∞ (mollifierKernel N n) := (mollifierBump N n).contDiff_normed

theorem mollifierKernel_hasCompactSupport (N n : ℕ) :
    HasCompactSupport (mollifierKernel N n) := (mollifierBump N n).hasCompactSupport_normed

theorem mollifierBump_radius_tendsto (N : ℕ) :
    Tendsto (fun n : ℕ => (mollifierBump N n).rOut) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [mollifierBump] using ht.const_mul 2

theorem mollifyKernel_ae_tendsto {N : ℕ} (f : SpatialL2 N) :
    ∀ᵐ x ∂volume, Tendsto (fun n : ℕ => mollify (mollifierKernel N n) f x)
      atTop (𝓝 (f x)) := by
  have hb : ∀ᶠ n : ℕ in atTop, (mollifierBump N n).rOut ≤ 2 * (mollifierBump N n).rIn :=
    Eventually.of_forall (fun _ => le_rfl)
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (mollifierBump_radius_tendsto N) hb ((Lp.memLp f).locallyIntegrable (by norm_num))
  simpa only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply,
    mollify, mollifierKernel] using hh

#print axioms mollifierKernel_integral
#print axioms mollifierKernel_contDiff
#print axioms mollifierKernel_hasCompactSupport
#print axioms mollifyKernel_ae_tendsto
end TheoremT.Continuum
