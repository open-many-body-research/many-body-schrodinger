import PolarThree_v1
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

/-! Differentiation of an actual finite sphere integral. All local dominating
bounds are derived from joint smoothness on compact radius-times-sphere sets.
No differentiability-under-integral premise is supplied by the caller. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

abbrev sphereMeasure : Measure (Metric.sphere (0 : E) 1) := (volume : Measure E).toSphere

def jointSphereAverage (G : ℝ × E → ℂ) (r : ℝ) : ℂ :=
  ∫ w : Metric.sphere (0 : E) 1, G (r, w.val) ∂sphereMeasure

def jointRadiusDerivative (G : ℝ × E → ℂ) (p : ℝ × E) : ℂ :=
  fderiv ℝ G p (1, 0)

theorem jointRadiusDerivative_contDiff {G : ℝ × E → ℂ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (jointRadiusDerivative G) :=
  ((contDiff_infty_iff_fderiv.mp hG).2).clm_apply contDiff_const

theorem jointSphereAverage_hasDerivAt {G : ℝ × E → ℂ} (hG : ContDiff ℝ ∞ G) (r : ℝ) :
    HasDerivAt (jointSphereAverage G) (jointSphereAverage (jointRadiusDerivative G) r) r := by
  have hDc := (jointRadiusDerivative_contDiff hG).continuous
  have hInt (s : ℝ) : Integrable
      (fun w : Metric.sphere (0 : E) 1 => G (s, w.val)) sphereMeasure :=
    (hG.continuous.comp (continuous_const.prodMk continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDInt (s : ℝ) : Integrable
      (fun w : Metric.sphere (0 : E) 1 => jointRadiusDerivative G (s, w.val)) sphereMeasure :=
    (hDc.comp (continuous_const.prodMk continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r 1).prod (isCompact_sphere (0 : E) 1)).exists_bound_of_continuousOn
    hDc.continuousOn
  have hd (s : ℝ) (w : Metric.sphere (0 : E) 1) :
      HasDerivAt (fun t : ℝ => G (t, w.val)) (jointRadiusDerivative G (s, w.val)) s := by
    have hp := (hasDerivAt_id s).prodMk (hasDerivAt_const s w.val)
    exact ((hG.differentiable (by simp) (s, w.val)).hasFDerivAt).comp_hasDerivAt s hp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s (w : Metric.sphere (0 : E) 1) => G (s, w.val))
    (F' := fun s (w : Metric.sphere (0 : E) 1) => jointRadiusDerivative G (s, w.val))
    (μ := sphereMeasure) (bound := fun _ => C)
    (Metric.ball_mem_nhds r zero_lt_one)
    (Filter.Eventually.of_forall (fun s => (hInt s).aestronglyMeasurable))
    (hInt r) (hDInt r).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w s hs => hC (s, w.val)
      ⟨Metric.ball_subset_closedBall hs, w.property⟩))
    (integrable_const C)
    (Filter.Eventually.of_forall (fun w s _ => hd s w))).2

theorem jointSphereAverage_deriv {G : ℝ × E → ℂ} (hG : ContDiff ℝ ∞ G) :
    deriv (jointSphereAverage G) = jointSphereAverage (jointRadiusDerivative G) :=
  funext (fun r => (jointSphereAverage_hasDerivAt hG r).deriv)

theorem jointSphereAverage_contDiff_nat (n : ℕ) : ∀ G : ℝ × E → ℂ,
    ContDiff ℝ ∞ G → ContDiff ℝ n (jointSphereAverage G) := by
  induction n with
  | zero =>
    intro G hG
    apply contDiff_zero.mpr
    exact (show Differentiable ℝ (jointSphereAverage G) from
      fun r => (jointSphereAverage_hasDerivAt hG r).differentiableAt).continuous
  | succ n ih =>
    intro G hG
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun r => (jointSphereAverage_hasDerivAt hG r).differentiableAt, by simp, ?_⟩
    rw [jointSphereAverage_deriv hG]
    exact ih _ (jointRadiusDerivative_contDiff hG)

theorem jointSphereAverage_contDiff {G : ℝ × E → ℂ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (jointSphereAverage G) :=
  contDiff_infty.mpr (fun n => jointSphereAverage_contDiff_nat n G hG)

#print axioms jointRadiusDerivative_contDiff
#print axioms jointSphereAverage_hasDerivAt
#print axioms jointSphereAverage_deriv
#print axioms jointSphereAverage_contDiff
end TheoremT.Polar
