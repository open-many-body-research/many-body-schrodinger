import ConfigurationL2Dominated_v1
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! Bounded continuous real-linear fields evaluated on actual complex L2
functions. This supplies the convergence step in a nonlinear weak chain rule. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace TheoremT.Continuum
set_option maxHeartbeats 800000

theorem nonlinearField_memLp {N : ℕ} (A : ℂ → ℂ →L[ℝ] ℂ) (hA : Continuous A)
    (K : ℝ≥0) (hb : ∀ z, ‖A z‖ ≤ K) (f d : SpatialL2 N) :
    MemLp (fun x => A (f x) (d x)) 2 volume := by
  apply (Lp.memLp d).of_le_mul
  · exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := ℂ) (F := ℂ)).continuous.comp_aestronglyMeasurable₂
      (hA.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
        (Lp.aestronglyMeasurable d)
  · exact Eventually.of_forall (fun x => (A (f x)).le_opNorm (d x) |>.trans
      (mul_le_mul_of_nonneg_right (hb (f x)) (norm_nonneg _)))

def nonlinearFieldL2 {N : ℕ} (A : ℂ → ℂ →L[ℝ] ℂ) (hA : Continuous A)
    (K : ℝ≥0) (hb : ∀ z, ‖A z‖ ≤ K) (f d : SpatialL2 N) : SpatialL2 N :=
  (nonlinearField_memLp A hA K hb f d).toLp (fun x => A (f x) (d x))

theorem nonlinearFieldL2_ae {N : ℕ} (A : ℂ → ℂ →L[ℝ] ℂ) (hA : Continuous A)
    (K : ℝ≥0) (hb : ∀ z, ‖A z‖ ≤ K) (f d : SpatialL2 N) :
    nonlinearFieldL2 A hA K hb f d =ᵐ[volume] (fun x => A (f x) (d x)) :=
  MemLp.coeFn_toLp _

theorem nonlinearFieldL2_norm_sub_le {N : ℕ} (A : ℂ → ℂ →L[ℝ] ℂ) (hA : Continuous A)
    (K : ℝ≥0) (hb : ∀ z, ‖A z‖ ≤ K) (f d e : SpatialL2 N) :
    ‖nonlinearFieldL2 A hA K hb f d - nonlinearFieldL2 A hA K hb f e‖ ≤
      K*‖d-e‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [nonlinearFieldL2_ae A hA K hb f d,
    nonlinearFieldL2_ae A hA K hb f e,
    Lp.coeFn_sub (nonlinearFieldL2 A hA K hb f d) (nonlinearFieldL2 A hA K hb f e),
    Lp.coeFn_sub d e] with x hd he hs hde
  simp only [Pi.sub_apply] at hs hde
  rw [hs,hd,he,hde,← map_sub]
  exact ((A (f x)).le_opNorm (d x-e x)).trans
    (mul_le_mul_of_nonneg_right (hb (f x)) (norm_nonneg _))

theorem nonlinearFieldL2_tendsto_ae {N : ℕ} (A : ℂ → ℂ →L[ℝ] ℂ) (hA : Continuous A)
    (K : ℝ≥0) (hb : ∀ z, ‖A z‖ ≤ K) (f : ℕ → SpatialL2 N) (f₀ d : SpatialL2 N)
    (hf : ∀ᵐ x, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x))) :
    Tendsto (fun n => nonlinearFieldL2 A hA K hb (f n) d) atTop
      (𝓝 (nonlinearFieldL2 A hA K hb f₀ d)) := by
  apply configuration_toLp_tendsto_dominated
    (fun n => nonlinearField_memLp A hA K hb (f n) d)
    (nonlinearField_memLp A hA K hb f₀ d)
    ((Lp.memLp d).norm.const_smul (K : ℝ))
  · intro n
    exact Eventually.of_forall (fun x => by
      simpa only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg K),abs_norm] using
        (A (f n x)).le_opNorm (d x) |>.trans
          (mul_le_mul_of_nonneg_right (hb (f n x)) (norm_nonneg _)))
  · exact Eventually.of_forall (fun x => by
      simpa only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg K),abs_norm] using
        (A (f₀ x)).le_opNorm (d x) |>.trans
          (mul_le_mul_of_nonneg_right (hb (f₀ x)) (norm_nonneg _)))
  · filter_upwards [hf] with x hx
    exact ((ContinuousLinearMap.apply ℝ ℂ (d x)).continuous.tendsto (A (f₀ x))).comp
      ((hA.tendsto (f₀ x)).comp hx)

theorem nonlinearFieldL2_tendsto {N : ℕ} (A : ℂ → ℂ →L[ℝ] ℂ) (hA : Continuous A)
    (K : ℝ≥0) (hb : ∀ z, ‖A z‖ ≤ K) (f d : ℕ → SpatialL2 N) (f₀ d₀ : SpatialL2 N)
    (hf : ∀ᵐ x, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hd : Tendsto d atTop (𝓝 d₀)) :
    Tendsto (fun n => nonlinearFieldL2 A hA K hb (f n) (d n)) atTop
      (𝓝 (nonlinearFieldL2 A hA K hb f₀ d₀)) := by
  have ht := nonlinearFieldL2_tendsto_ae A hA K hb f f₀ d₀ hf
  have he : Tendsto (fun n => nonlinearFieldL2 A hA K hb (f n) (d n) -
      nonlinearFieldL2 A hA K hb (f n) d₀) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => nonlinearFieldL2_norm_sub_le A hA K hb (f n) (d n) d₀)
    simpa using (tendsto_const_nhds (x := (K : ℝ))).mul
      ((hd.sub (tendsto_const_nhds (x := d₀))).norm)
  simpa only [sub_add_cancel,zero_add] using he.add ht

#print axioms nonlinearField_memLp
#print axioms nonlinearFieldL2_norm_sub_le
#print axioms nonlinearFieldL2_tendsto
end TheoremT.Continuum
