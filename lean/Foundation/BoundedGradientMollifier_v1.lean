import MollifierSequence_v2
import ConfigurationDerivativeNorm_v1
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual normalized mollifications of weak derivatives have a uniform
Lipschitz bound when the weak gradient is essentially bounded. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ContDiff Topology NNReal ENNReal
namespace TheoremT.Continuum

theorem mollify_norm_le_of_ae_bound {N : ℕ} (f : SpatialL2 N) {M : ℝ}
    (hM : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) (n : ℕ) (x : Configuration N) :
    ‖mollify (mollifierKernel N n) f x‖ ≤ M := by
  have hi : Integrable (fun y => mollifierKernel N n (x-y)) volume :=
    ((volume.measurePreserving_sub_left x).integrable_comp
      (mollifierKernel_integrable N n).aestronglyMeasurable).mpr
      (mollifierKernel_integrable N n)
  have hb := norm_integral_le_of_norm_le
    (f := fun y => mollifierKernel N n (x-y) • f y) (hi.mul_const M) (hM.mono (fun y hy => by
    simpa only [norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (mollifierKernel_nonneg N n (x-y))] using
      mul_le_mul_of_nonneg_left hy (mollifierKernel_nonneg N n (x-y))))
  change ‖mollify (mollifierKernel N n) f x‖ ≤ _ at hb
  have he : (∫ y, mollifierKernel N n (x-y))=1 := by
    rw [integral_sub_left_eq_self]
    exact mollifierKernel_integral N n
  simpa only [integral_mul_const,he,one_mul] using hb

theorem weak_gradient_mollifications_uniform_lipschitz {N : ℕ}
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hdtop : ∀ k, MemLp (d k) ⊤ volume) :
    ∃ K : ℝ≥0, ∀ n : ℕ, LipschitzWith K (mollify (mollifierKernel N n) f) := by
  classical
  have hb (k : Coordinate N) : ∃ C : ℝ≥0, ∀ᵐ x ∂volume, ‖d k x‖₊ ≤ C := by
    apply eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    simpa only [eLpNorm_exponent_top] using (hdtop k).eLpNorm_lt_top
  choose C hC using hb
  refine ⟨∑ k, C k, fun n => ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((mollify_contDiff _ (mollifierKernel_contDiff N n)
      (mollifierKernel_hasCompactSupport N n) f).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (mollify (mollifierKernel N n) f) x‖ ≤ ((∑ k, C k : ℝ≥0) : ℝ)
  rw [NNReal.coe_sum]
  apply (configuration_clm_norm_le_sum N _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [mollify_derivative (hd k) _ (mollifierKernel_contDiff N n)
    (mollifierKernel_hasCompactSupport N n)]
  exact mollify_norm_le_of_ae_bound (d k) ((hC k).mono (fun x hx => hx)) n x

#print axioms mollify_norm_le_of_ae_bound
#print axioms weak_gradient_mollifications_uniform_lipschitz
end TheoremT.Continuum
