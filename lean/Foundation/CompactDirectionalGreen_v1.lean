import CompactRealDirectionalIntegral_v1
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_real_inner_integrable_general {u w : E → F}
    (hu : Continuous u) (hw : Continuous w) (hc : HasCompactSupport u) :
    Integrable (fun x => inner ℝ (u x) (w x)) μ := by
  apply (hu.inner (𝕜 := ℝ) hw).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  change u x ≠ 0
  intro hz
  apply hx
  simp [hz]

theorem compact_directional_green {u : E → F}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (v : E) :
    (∫ x, ‖fderiv ℝ u x v‖^2 ∂μ) =
      -(∫ x, inner ℝ (u x) (fderiv ℝ (fun y => fderiv ℝ u y v) x v) ∂μ) := by
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ u x v) :=
    (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdd : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ u y v) x v) :=
    (hd.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hh := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := μ)
    (B := innerSL ℝ) (v := v)
    (compact_real_inner_integrable_general hd.continuous hd.continuous (hc.fderiv_apply ℝ v))
    (compact_real_inner_integrable_general hu.continuous hdd.continuous hc)
    (compact_real_inner_integrable_general hu.continuous hd.continuous hc)
    (fun x _ => hu.differentiable (by simp) x)
    (fun x _ => hd.differentiable (by simp) x)
  change (∫ x, inner ℝ (u x) (fderiv ℝ (fun y => fderiv ℝ u y v) x v) ∂μ) =
    -(∫ x, inner ℝ (fderiv ℝ u x v) (fderiv ℝ u x v) ∂μ) at hh
  simp only [real_inner_self_eq_norm_sq] at hh
  linarith

#print axioms compact_real_inner_integrable_general
#print axioms compact_directional_green
end TheoremT.Continuum
