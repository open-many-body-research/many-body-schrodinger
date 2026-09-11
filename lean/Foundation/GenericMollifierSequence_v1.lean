import GenericWeakMollification_v1
import RealKernelConvolutionL2Generic_v1
import HardyMollifierStrong_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Convolution
namespace TheoremT.Continuum.GenericMollifier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def mollifierBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := ((n : ℝ) + 1)⁻¹
  rOut := 2 * ((n : ℝ) + 1)⁻¹
  rIn_pos := inv_pos.mpr (by positivity)
  rIn_lt_rOut := by
    have h : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
    linarith

def mollifierKernel (n : ℕ) : E → ℝ :=
  (mollifierBump (E := E) n).normed volume

theorem mollifierKernel_nonneg (n : ℕ) (x : E) :
    0 ≤ mollifierKernel (E := E) n x := (mollifierBump (E := E) n).nonneg_normed x

theorem mollifierKernel_integral (n : ℕ) :
    (∫ x, mollifierKernel (E := E) n x) = 1 := (mollifierBump (E := E) n).integral_normed

theorem mollifierKernel_integrable (n : ℕ) :
    Integrable (mollifierKernel (E := E) n) := (mollifierBump (E := E) n).integrable_normed

theorem mollifierKernel_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (mollifierKernel (E := E) n) := (mollifierBump (E := E) n).contDiff_normed

theorem mollifierKernel_hasCompactSupport (n : ℕ) :
    HasCompactSupport (mollifierKernel (E := E) n) := (mollifierBump (E := E) n).hasCompactSupport_normed

theorem mollifierBump_radius_tendsto  :
    Tendsto (fun n : ℕ => (mollifierBump (E := E) n).rOut) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [mollifierBump] using ht.const_mul 2

theorem mollifyKernel_ae_tendsto (f : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂volume, Tendsto (fun n : ℕ => mollify (mollifierKernel (E := E) n) f x)
      atTop (𝓝 (f x)) := by
  have hb : ∀ᶠ n : ℕ in atTop, (mollifierBump (E := E) n).rOut ≤ 2 * (mollifierBump (E := E) n).rIn :=
    Eventually.of_forall (fun _ => le_rfl)
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (mollifierBump_radius_tendsto (E := E)) hb ((Lp.memLp f).locallyIntegrable (by norm_num))
  simpa only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply,
    mollify, mollifierKernel] using hh


theorem mollify_eq_normalized_orientation (η : E → ℝ)
    (f : Lp ℂ 2 (volume : Measure E)) :
    mollify η f = (fun x => ∫ t, η t • f (x-t)) := by
  change ((f : E → ℂ) ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip, volume] η) =
    (η ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ), volume]
      (f : E → ℂ))
  exact convolution_flip (f := η) (g := (f : E → ℂ))
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) (μ := volume)

theorem mollifier_memLp (n : ℕ) (f : Lp ℂ 2 (volume : Measure E)) :
    MemLp (mollify (mollifierKernel n) f) 2 volume := by
  rw [mollify_eq_normalized_orientation]
  exact real_kernel_convolution_l2_memLp
    (mollifierKernel_contDiff n).continuous.stronglyMeasurable
    (mollifierKernel_integrable n) (Lp.stronglyMeasurable f) (Lp.memLp f)

def mollifyLp (n : ℕ) (f : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure E) :=
  (mollifier_memLp n f).toLp (mollify (mollifierKernel n) f)

theorem mollifyLp_ae (n : ℕ) (f : Lp ℂ 2 (volume : Measure E)) :
    mollifyLp n f =ᵐ[volume] mollify (mollifierKernel n) f :=
  (mollifier_memLp n f).coeFn_toLp

theorem mollifyLp_norm_le (n : ℕ) (f : Lp ℂ 2 (volume : Measure E)) :
    ‖mollifyLp n f‖ ≤ ‖f‖ := by
  have hb := real_kernel_convolution_l2_norm_le
    (mollifierKernel_contDiff (E := E) n).continuous.stronglyMeasurable
    (mollifierKernel_integrable n) (Lp.stronglyMeasurable f) (Lp.memLp f)
  have hn : (∫ s, ‖mollifierKernel (E := E) n s‖) = 1 := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (mollifierKernel_nonneg n _)]
    exact mollifierKernel_integral n
  rw [hn, one_mul] at hb
  have he : mollifyLp n f =
      (real_kernel_convolution_l2_memLp
        (mollifierKernel_contDiff n).continuous.stronglyMeasurable
        (mollifierKernel_integrable n) (Lp.stronglyMeasurable f) (Lp.memLp f)).toLp
        (fun t => ∫ s, mollifierKernel n s • f (t-s)) := by
    apply Lp.ext
    filter_upwards [mollifyLp_ae n f,
      (real_kernel_convolution_l2_memLp
        (mollifierKernel_contDiff n).continuous.stronglyMeasurable
        (mollifierKernel_integrable n) (Lp.stronglyMeasurable f) (Lp.memLp f)).coeFn_toLp]
      with x hx hy
    rw [hx, hy, mollify_eq_normalized_orientation]
  rw [he]
  simpa using hb

theorem mollifyLp_ae_tendsto (f : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂volume, Tendsto (fun n : ℕ => mollifyLp n f x) atTop (𝓝 (f x)) := by
  have ha : ∀ᵐ x ∂volume, ∀ n : ℕ, mollifyLp n f x = mollify (mollifierKernel n) f x := by
    rw [ae_all_iff]
    intro n
    exact mollifyLp_ae n f
  filter_upwards [ha, mollifyKernel_ae_tendsto f] with x hx hlim
  simpa only [hx] using hlim

theorem mollifyLp_tendsto (f : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun n : ℕ => mollifyLp n f) atTop (𝓝 f) :=
  TheoremT.HardyLimit.l2_tendsto_of_ae_tendsto_norm_le _ _
    (mollifyLp_ae_tendsto f) (fun n => mollifyLp_norm_le n f)

end TheoremT.Continuum.GenericMollifier
