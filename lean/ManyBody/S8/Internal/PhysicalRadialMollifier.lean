import ManyBody.S8.Internal.PhysicalRadialCompactCutoff
import HardySobolevDensity_v1
import RealKernelConvolutionL2Generic_v1
import GenericMollifierSequence_v1
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! A literal norm-radial normalized physical approximate identity. The kernel
is fixed before states and is invariant under every genuine configuration
linear isometry; no symmetry of a classically selected bump is assumed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Metric Set Function
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalRadialMollifierRadius (m : ℕ) : ℝ := ((m:ℝ)+1)⁻¹

theorem physicalRadialMollifierRadius_pos (m : ℕ) : 0<physicalRadialMollifierRadius m := by
  unfold physicalRadialMollifierRadius
  positivity

theorem physicalRadialMollifierRadius_le_one (m : ℕ) : physicalRadialMollifierRadius m≤1 := by
  unfold physicalRadialMollifierRadius
  exact (inv_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])

def physicalRadialMollifierMass (m : ℕ) : ℝ :=
  ∫ x : Configuration 2, physicalRadialCompactCutoff (physicalRadialMollifierRadius m) x

theorem physicalRadialMollifierCutoff_integrable (m : ℕ) :
    Integrable (physicalRadialCompactCutoff (physicalRadialMollifierRadius m)) :=
  (physicalRadialCompactCutoff_contDiff _).continuous.integrable_of_hasCompactSupport
    (physicalRadialCompactCutoff_hasCompactSupport (physicalRadialMollifierRadius_pos m))

theorem physicalRadialMollifierMass_lower (m : ℕ) :
    volume.real (closedBall (0 : Configuration 2) (physicalRadialMollifierRadius m))≤
      physicalRadialMollifierMass m := by
  calc _=(∫ x : Configuration 2 in closedBall 0 (physicalRadialMollifierRadius m), (1:ℝ)) := by simp
       _=(∫ x : Configuration 2 in closedBall 0 (physicalRadialMollifierRadius m),
         physicalRadialCompactCutoff (physicalRadialMollifierRadius m) x) :=
         setIntegral_congr_fun measurableSet_closedBall (fun x hx =>
           (physicalRadialCompactCutoff_eq_one (physicalRadialMollifierRadius_pos m)
             (mem_closedBall_zero_iff.mp hx)).symm)
       _≤physicalRadialMollifierMass m :=
         setIntegral_le_integral (physicalRadialMollifierCutoff_integrable m)
           (Eventually.of_forall (fun x => physicalRadialCompactCutoff_nonneg _ x))

theorem physicalRadialMollifierMass_pos (m : ℕ) : 0<physicalRadialMollifierMass m :=
  (ENNReal.toReal_pos (measure_closedBall_pos volume (0 : Configuration 2)
    (physicalRadialMollifierRadius_pos m)).ne' measure_closedBall_lt_top.ne).trans_le
      (physicalRadialMollifierMass_lower m)

def physicalRadialMollifierKernel (m : ℕ) (x : Configuration 2) : ℝ :=
  physicalRadialCompactCutoff (physicalRadialMollifierRadius m) x / physicalRadialMollifierMass m

theorem physicalRadialMollifierKernel_nonneg (m : ℕ) (x : Configuration 2) :
    0≤physicalRadialMollifierKernel m x :=
  div_nonneg (physicalRadialCompactCutoff_nonneg _ _) (physicalRadialMollifierMass_pos m).le

theorem physicalRadialMollifierKernel_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (physicalRadialMollifierKernel m) :=
  (physicalRadialCompactCutoff_contDiff _).div_const _

theorem physicalRadialMollifierKernel_hasCompactSupport (m : ℕ) :
    HasCompactSupport (physicalRadialMollifierKernel m) :=
  by
    have hc := physicalRadialCompactCutoff_hasCompactSupport (physicalRadialMollifierRadius_pos m)
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    exact hc.mono fun x hx => by
      change physicalRadialCompactCutoff (physicalRadialMollifierRadius m) x=0 at hx
      change physicalRadialMollifierKernel m x=0
      simp only [physicalRadialMollifierKernel,hx,zero_div]

theorem physicalRadialMollifierKernel_integrable (m : ℕ) :
    Integrable (physicalRadialMollifierKernel m) :=
  (physicalRadialMollifierCutoff_integrable m).div_const _

theorem physicalRadialMollifierKernel_integral (m : ℕ) :
    (∫ x, physicalRadialMollifierKernel m x)=1 := by
  simp only [physicalRadialMollifierKernel,integral_div]
  exact div_self (physicalRadialMollifierMass_pos m).ne'

theorem physicalRadialMollifierKernel_isometry (m : ℕ)
    (Q : Configuration 2 ≃ₗᵢ[ℝ] Configuration 2) (x : Configuration 2) :
    physicalRadialMollifierKernel m (Q x)=physicalRadialMollifierKernel m x := by
  rw [physicalRadialMollifierKernel,physicalRadialMollifierKernel,
    physicalRadialCompactCutoff_isometry]

theorem physicalRadialMollifierKernel_neg (m : ℕ) (x : Configuration 2) :
    physicalRadialMollifierKernel m (-x)=physicalRadialMollifierKernel m x :=
  physicalRadialMollifierKernel_isometry m (LinearIsometryEquiv.neg ℝ) x

theorem physicalRadialMollifierKernel_support (m : ℕ) :
    Function.support (physicalRadialMollifierKernel m)⊆
      closedBall (0 : Configuration 2) (2*physicalRadialMollifierRadius m) := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hzero := physicalRadialCompactCutoff_eq_zero (physicalRadialMollifierRadius_pos m)
    (show (3/2)*physicalRadialMollifierRadius m≤‖x‖ by
      have hp := physicalRadialMollifierRadius_pos m
      linarith [lt_of_not_ge hn])
  exact hx (by simp [physicalRadialMollifierKernel,hzero])

theorem physicalRadialMollifierMass_outer_lower (m : ℕ) :
    volume.real (closedBall (0 : Configuration 2) (2*physicalRadialMollifierRadius m)) /
      2^Module.finrank ℝ (Configuration 2)≤physicalRadialMollifierMass m := by
  apply le_trans _ (physicalRadialMollifierMass_lower m)
  rw [div_le_iff₀ (by positivity),
    addHaar_real_closedBall' _ _ (physicalRadialMollifierRadius_pos m).le,
    addHaar_real_closedBall' _ _ (mul_nonneg (by norm_num) (physicalRadialMollifierRadius_pos m).le),
    mul_pow]
  ring_nf
  exact le_rfl

theorem physicalRadialMollifierKernel_bound (m : ℕ) (x : Configuration 2) :
    physicalRadialMollifierKernel m x≤2^Module.finrank ℝ (Configuration 2) /
      volume.real (closedBall (0 : Configuration 2) (2*physicalRadialMollifierRadius m)) := by
  have hp : 0<volume.real (closedBall (0 : Configuration 2) (2*physicalRadialMollifierRadius m)) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume _ (mul_pos (by norm_num) (physicalRadialMollifierRadius_pos m))).ne'
      measure_closedBall_lt_top.ne
  have hb : physicalRadialMollifierKernel m x≤1/physicalRadialMollifierMass m := by
    unfold physicalRadialMollifierKernel
    exact div_le_div_of_nonneg_right (physicalRadialCompactCutoff_le_one _ _)
      (physicalRadialMollifierMass_pos m).le
  apply hb.trans
  rw [div_le_div_iff₀ (physicalRadialMollifierMass_pos m) hp,one_mul,
    ← div_le_iff₀' (by positivity : (0:ℝ)<2^Module.finrank ℝ (Configuration 2))]
  exact physicalRadialMollifierMass_outer_lower m

theorem physicalRadialMollifierRadius_tendsto :
    Tendsto physicalRadialMollifierRadius atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => ((m:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ))
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem physicalRadialMollify_ae_tendsto (f : SpatialL2 2) :
    ∀ᵐ x ∂volume, Tendsto (fun m => mollify (physicalRadialMollifierKernel m) f x)
      atTop (𝓝 (f x)) := by
  have hg : LocallyIntegrable (f : Configuration 2 → ℂ) volume :=
    (Lp.memLp f).locallyIntegrable (by norm_num)
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average_norm_sub hg] with x h0
  have hr : Tendsto (fun m => 2*physicalRadialMollifierRadius m) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using physicalRadialMollifierRadius_tendsto.const_mul 2,
      Eventually.of_forall (fun m => by change 0<2*physicalRadialMollifierRadius m; exact mul_pos (by norm_num) (physicalRadialMollifierRadius_pos m))⟩
  have ht := (h0.comp (Besicovitch.tendsto_filterAt volume x)).comp hr
  apply tendsto_integral_smul_of_tendsto_average_norm_sub (2^Module.finrank ℝ (Configuration 2)) ht
  · filter_upwards with m using hg.integrableOn_isCompact (isCompact_closedBall _ _)
  · apply tendsto_const_nhds.congr (fun m => ?_)
    rw [← integral_neg_eq_self]
    simp only [sub_neg_eq_add,integral_add_left_eq_self,physicalRadialMollifierKernel_integral]
  · filter_upwards with m
    intro y hy
    have hm := physicalRadialMollifierKernel_support m hy
    simpa only [mem_closedBall,dist_eq_norm_sub'] using (mem_closedBall_zero_iff.mp hm)
  · filter_upwards with m
    intro y
    rw [abs_of_nonneg (physicalRadialMollifierKernel_nonneg m _),addHaar_real_closedBall_center]
    exact physicalRadialMollifierKernel_bound m _

theorem physicalRadialMollify_memLp (m : ℕ) (f : SpatialL2 2) :
    MemLp (mollify (physicalRadialMollifierKernel m) f) 2 volume := by
  rw [show mollify (physicalRadialMollifierKernel m) f=
      (fun x => ∫ t,physicalRadialMollifierKernel m t • f (x-t)) from
    GenericMollifier.mollify_eq_normalized_orientation _ f]
  exact real_kernel_convolution_l2_memLp
    (physicalRadialMollifierKernel_contDiff m).continuous.stronglyMeasurable
    (physicalRadialMollifierKernel_integrable m) (Lp.stronglyMeasurable f) (Lp.memLp f)

def physicalRadialMollifyLp (m : ℕ) (f : SpatialL2 2) : SpatialL2 2 :=
  (physicalRadialMollify_memLp m f).toLp (mollify (physicalRadialMollifierKernel m) f)

theorem physicalRadialMollifyLp_ae (m : ℕ) (f : SpatialL2 2) :
    (physicalRadialMollifyLp m f : Configuration 2 → ℂ)=ᵐ[volume]
      mollify (physicalRadialMollifierKernel m) f :=
  (physicalRadialMollify_memLp m f).coeFn_toLp

theorem physicalRadialMollifyLp_norm_le (m : ℕ) (f : SpatialL2 2) :
    ‖physicalRadialMollifyLp m f‖≤‖f‖ := by
  have hb := real_kernel_convolution_l2_norm_le
    (physicalRadialMollifierKernel_contDiff m).continuous.stronglyMeasurable
    (physicalRadialMollifierKernel_integrable m) (Lp.stronglyMeasurable f) (Lp.memLp f)
  have hn : (∫ t,‖physicalRadialMollifierKernel m t‖)=1 := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (physicalRadialMollifierKernel_nonneg m _)]
    exact physicalRadialMollifierKernel_integral m
  rw [hn,one_mul] at hb
  have hclass : physicalRadialMollifyLp m f =
      (real_kernel_convolution_l2_memLp
        (physicalRadialMollifierKernel_contDiff m).continuous.stronglyMeasurable
        (physicalRadialMollifierKernel_integrable m) (Lp.stronglyMeasurable f) (Lp.memLp f)).toLp
        (fun x => ∫ t,physicalRadialMollifierKernel m t • f (x-t)) := by
    apply Lp.ext
    exact (physicalRadialMollifyLp_ae m f).trans (Filter.EventuallyEq.of_eq
      (GenericMollifier.mollify_eq_normalized_orientation _ f)) |>.trans
        (real_kernel_convolution_l2_memLp
          (physicalRadialMollifierKernel_contDiff m).continuous.stronglyMeasurable
          (physicalRadialMollifierKernel_integrable m) (Lp.stronglyMeasurable f)
          (Lp.memLp f)).coeFn_toLp.symm
  rw [hclass]
  simpa using hb

theorem physicalRadialMollifyLp_tendsto (f : SpatialL2 2) :
    Tendsto (fun m => physicalRadialMollifyLp m f) atTop (𝓝 f) := by
  have heq : ∀ᵐ x ∂volume, ∀ m : ℕ,
      physicalRadialMollifyLp m f x=mollify (physicalRadialMollifierKernel m) f x := by
    rw [ae_all_iff]
    intro m
    exact physicalRadialMollifyLp_ae m f
  have ht : ∀ᵐ x ∂volume, Tendsto (fun m => physicalRadialMollifyLp m f x) atTop (𝓝 (f x)) := by
    filter_upwards [heq,physicalRadialMollify_ae_tendsto f] with x hx ht
    simpa only [hx] using ht
  exact TheoremT.HardyLimit.l2_tendsto_of_ae_tendsto_norm_le _ _ ht
    (fun m => physicalRadialMollifyLp_norm_le m f)

#print axioms physicalRadialMollifierKernel_integral
#print axioms physicalRadialMollifierKernel_isometry
#print axioms physicalRadialMollify_ae_tendsto
#print axioms physicalRadialMollifyLp_tendsto
end ManyBody.S8
