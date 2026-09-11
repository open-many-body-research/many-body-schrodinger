import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! The compact primitive of an actual smooth real test function of integral
zero. This is a prerequisite for proving that a weak derivative vanishes
only on constant functions; no weak ODE conclusion is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.OneDimensional

theorem smooth_compact_primitive (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (hab : a < b) (hs : Function.support f ⊆ Ioo a b)
    (hz : ∫ x, f x = 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ Icc a b ∧ deriv F = f := by
  let F : ℝ → ℝ := fun x => ∫ t in a..x, f t
  have hd : ∀ x, HasDerivAt F (f x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.continuous.intervalIntegrable a x)
      (hf.continuous.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuous.continuousAt
  have hder : deriv F = f := funext (fun x => (hd x).deriv)
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun x => (hd x).differentiableAt, hder.symm ▸ hf⟩
  have hleft : ∀ x, x ≤ a → F x = 0 := by
    intro x hx
    have heq : (∫ t in a..x, f t) = ∫ t in a..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hx] at ht
      by_contra hnot
      have hmem : t ∈ Function.support f := hnot
      have hlt := (hs hmem).1
      exact (not_lt_of_ge ht.2) hlt
    simpa [F] using heq
  have hright : ∀ x, b ≤ x → F x = 0 := by
    intro x hx
    change (∫ t in a..x, f t) = 0
    rw [intervalIntegral.integral_eq_integral_of_support_subset]
    · exact hz
    · intro t ht
      exact ⟨(hs ht).1, (hs ht).2.le.trans hx⟩
  have hsF : Function.support F ⊆ Icc a b := by
    intro x hx
    constructor
    · by_contra hnot
      exact hx (hleft x (le_of_lt (lt_of_not_ge hnot)))
    · by_contra hnot
      exact hx (hright x (le_of_lt (lt_of_not_ge hnot)))
  have htF : tsupport F ⊆ Icc a b :=
    closure_minimal hsF isClosed_Icc
  refine ⟨F,hF,?_,htF,hder⟩
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsF

#print axioms smooth_compact_primitive
end TheoremT.OneDimensional
