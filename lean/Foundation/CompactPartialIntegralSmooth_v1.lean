import CompactPartialIntegralDerivative_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
universe u v
variable {Y F : Type u} {T : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasureOnCompacts μ]

theorem compactPartialIntegral_contDiff_nat (n : ℕ) {G : Y × T → F}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    ContDiff ℝ n (compactPartialIntegral (μ := μ) G) := by
  induction n generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    exact (show Differentiable ℝ (compactPartialIntegral (μ := μ) G) from
      fun y => (compactPartialIntegral_hasFDerivAt hG hc y).differentiableAt).continuous
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
    refine ⟨fun y => (compactPartialIntegral_hasFDerivAt hG hc y).differentiableAt,by simp,?_⟩
    rw [compactPartialIntegral_fderiv hG hc]
    exact ih (firstParameterFDeriv_contDiff hG) (firstParameterFDeriv_hasCompactSupport hc)

theorem compactPartialIntegral_contDiff {G : Y × T → F}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    ContDiff ℝ ∞ (compactPartialIntegral (μ := μ) G) :=
  contDiff_infty.mpr (fun n => compactPartialIntegral_contDiff_nat n hG hc)

#print axioms compactPartialIntegral_contDiff_nat
#print axioms compactPartialIntegral_contDiff
end TheoremT.Continuum
