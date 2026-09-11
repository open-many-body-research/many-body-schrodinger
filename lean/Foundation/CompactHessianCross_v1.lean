import CompactInnerCoordinate_v1
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem smooth_second_directional_commute {u : E → F}
    (hu : ContDiff ℝ ∞ u) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ u y v) x w =
      fderiv ℝ (fun y => fderiv ℝ u y w) x v := by
  have hD := (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).differentiable (by simp) x
  simp only [fderiv_clm_apply hD (differentiableAt_const v),
    fderiv_clm_apply hD (differentiableAt_const w),fderiv_const_apply,
    ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)).eq w v

theorem compact_second_directional_cross
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (v w : E) :
    (∫ x, inner ℝ (fderiv ℝ (fun y => fderiv ℝ u y v) x v)
      (fderiv ℝ (fun y => fderiv ℝ u y w) x w) ∂μ) =
    ∫ x, ‖fderiv ℝ (fun y => fderiv ℝ u y v) x w‖^2 ∂μ := by
  have hd (q : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ u x q) :=
    (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdd (q r : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ u y q) x r) :=
    ((hd q).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have h1 := compact_directional_inner_ibp (μ := μ) (hd v) (hdd w w) (hc.fderiv_apply ℝ v) v
  have h2 := compact_directional_inner_ibp (μ := μ) (hd v) (hdd w v) (hc.fderiv_apply ℝ v) w
  have he (x : E) := smooth_second_directional_commute (hd w) x w v
  simp_rw [he] at h1
  rw [h2] at h1
  have hs (x : E) := smooth_second_directional_commute hu x w v
  simp_rw [hs,real_inner_self_eq_norm_sq] at h1
  linarith

#print axioms smooth_second_directional_commute
#print axioms compact_second_directional_cross
end TheoremT.Continuum
