import GenericMollifierSequence_v1
import PartialSpectatorSmoothKernel_v1
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology ContDiff Convolution
namespace TheoremT.Continuum
open GenericMollifier
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem partial_mollifier_ae_tendsto (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    ∀ᵐ p ∂volume, Tendsto (fun n : ℕ =>
      partialSpectatorConvolution (ν := volume) (GenericMollifier.mollifierKernel (E := T) n) f p)
      atTop (𝓝 (f p)) := by
  have hM (n : ℕ) : Measurable
      (partialSpectatorConvolution (ν := volume) (GenericMollifier.mollifierKernel (E := T) n) f) :=
    (partialSpectatorConvolution_stronglyMeasurable
      (GenericMollifier.mollifierKernel_contDiff n).continuous.stronglyMeasurable (Lp.stronglyMeasurable f)).measurable
  change ∀ᵐ p ∂(volume : Measure Y).prod volume, _
  apply (ae_prod_iff_ae_ae (measurableSet_tendsto_fun hM (Lp.stronglyMeasurable f).measurable)).mpr
  filter_upwards [memLp_two_product_slices_ae (Lp.memLp f)] with y hy
  have hb : ∀ᶠ n : ℕ in atTop, (GenericMollifier.mollifierBump (E := T) n).rOut ≤
      2 * (GenericMollifier.mollifierBump (E := T) n).rIn := Eventually.of_forall (fun _ => le_rfl)
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (GenericMollifier.mollifierBump_radius_tendsto (E := T)) hb (hy.locallyIntegrable (by norm_num))
  simpa only [convolution_def,ContinuousLinearMap.lsmul_apply,GenericMollifier.mollifierKernel,
    partialSpectatorConvolution] using hh

def partialMollifyLp (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    Lp ℂ 2 (volume : Measure (Y × T)) :=
  (partialSpectatorConvolution_ae_memLp_two (GenericMollifier.mollifierKernel_integrable (E := T) n)
    (Lp.memLp f)).toLp (partialSpectatorConvolution (ν := volume) (GenericMollifier.mollifierKernel (E := T) n) f)

theorem partialMollifyLp_ae (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    partialMollifyLp n f =ᵐ[volume]
      partialSpectatorConvolution (ν := volume) (GenericMollifier.mollifierKernel (E := T) n) f :=
  (partialSpectatorConvolution_ae_memLp_two (GenericMollifier.mollifierKernel_integrable n) (Lp.memLp f)).coeFn_toLp

theorem partialMollifyLp_norm_le (n : ℕ) (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    ‖partialMollifyLp n f‖ ≤ ‖f‖ := by
  have hb := partialSpectatorConvolution_ae_norm_le (GenericMollifier.mollifierKernel_integrable (E := T) n) (Lp.memLp f)
  have hn : (∫ s, ‖GenericMollifier.mollifierKernel (E := T) n s‖) = 1 := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (GenericMollifier.mollifierKernel_nonneg n _)]
    exact GenericMollifier.mollifierKernel_integral n
  rw [hn,one_mul,Lp.toLp_coeFn] at hb
  exact hb

theorem partialMollifyLp_ae_tendsto (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    ∀ᵐ p ∂volume, Tendsto (fun n : ℕ => partialMollifyLp n f p) atTop (𝓝 (f p)) := by
  have he : ∀ᵐ p ∂volume, ∀ n : ℕ, partialMollifyLp n f p =
      partialSpectatorConvolution (ν := volume) (GenericMollifier.mollifierKernel (E := T) n) f p := by
    rw [ae_all_iff]
    intro n
    exact partialMollifyLp_ae n f
  filter_upwards [he,partial_mollifier_ae_tendsto f] with p hp hlim
  simpa only [hp] using hlim

theorem partialMollifyLp_tendsto (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    Tendsto (fun n : ℕ => partialMollifyLp n f) atTop (𝓝 f) :=
  TheoremT.HardyLimit.l2_tendsto_of_ae_tendsto_norm_le _ _
    (partialMollifyLp_ae_tendsto f) (fun n => partialMollifyLp_norm_le n f)

#print axioms partial_mollifier_ae_tendsto
#print axioms partialMollifyLp
#print axioms partialMollifyLp_ae
#print axioms partialMollifyLp_norm_le
#print axioms partialMollifyLp_ae_tendsto
#print axioms partialMollifyLp_tendsto
end TheoremT.Continuum
