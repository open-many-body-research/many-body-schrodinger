import WeakDerivativeConstant_v1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Actual compact tests multiplied by the hydrogen radial integrating factor.
The apparent singularity at zero is harmless because the tests vanish in a
neighborhood of zero. All derivatives below are actual derivatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.OneDimensional

def radialWeight (Z x : ℝ) : ℝ := Real.exp (Z*x)/x

theorem radialWeight_continuousOn (Z : ℝ) :
    ContinuousOn (radialWeight Z) (Ioi (0 : ℝ)) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div
    continuousOn_id (fun x hx => ne_of_gt hx)

theorem radialWeight_hasDerivAt (Z x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (radialWeight Z) ((Z-x⁻¹)*radialWeight Z x) x := by
  have h : HasDerivAt (fun y : ℝ => Real.exp (Z*y)/y)
      ((Real.exp (Z*x)*Z*x-Real.exp (Z*x))/x^2) x := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id x).const_mul Z).exp.fun_div (hasDerivAt_id x) hx)
  have he : (Z-x⁻¹)*radialWeight Z x =
      (Real.exp (Z*x)*Z*x-Real.exp (Z*x))/x^2 := by
    dsimp [radialWeight]
    field_simp
    <;> ring
  rw [he]
  exact h

theorem radial_weighted_test_contDiff (Z : ℝ) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (fun x => ψ x*radialWeight Z x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hn : (0 : ℝ) ∉ tsupport ψ := by
      intro h
      exact (lt_irrefl (0 : ℝ)) (hs h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]
  · exact hψ.contDiffAt.mul
      (((contDiffAt_const.mul contDiffAt_id).exp).div contDiffAt_id hx)

theorem radial_weighted_test_compact (Z : ℝ) (ψ : ℝ → ℝ)
    (hc : HasCompactSupport ψ) :
    HasCompactSupport (fun x => ψ x*radialWeight Z x) := hc.mul_right

theorem radial_weighted_test_tsupport (Z : ℝ) (ψ : ℝ → ℝ)
    (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    tsupport (fun x => ψ x*radialWeight Z x) ⊆ Ioi (0 : ℝ) :=
  tsupport_mul_subset_left.trans hs

theorem radial_weighted_test_identity (Z : ℝ) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    -deriv (fun y => ψ y*radialWeight Z y) x
      -(ψ x*radialWeight Z x)/x+Z*(ψ x*radialWeight Z x)
      = -deriv ψ x*radialWeight Z x := by
  by_cases hx : x = 0
  · subst x
    have hn : (0 : ℝ) ∉ tsupport ψ := by
      intro h
      exact (lt_irrefl (0 : ℝ)) (hs h)
    have hnθ : (0 : ℝ) ∉ tsupport (fun x => ψ x*radialWeight Z x) :=
      fun h => hn (tsupport_mul_subset_left h)
    rw [deriv_of_notMem_tsupport hnθ,deriv_of_notMem_tsupport hn]
    simp [radialWeight]
  · rw [((hψ.differentiable (by simp) x).hasDerivAt.fun_mul
      (radialWeight_hasDerivAt Z x hx)).deriv]
    simp only [div_eq_mul_inv]
    ring

#print axioms radialWeight_continuousOn
#print axioms radialWeight_hasDerivAt
#print axioms radial_weighted_test_contDiff
#print axioms radial_weighted_test_compact
#print axioms radial_weighted_test_tsupport
#print axioms radial_weighted_test_identity
end TheoremT.OneDimensional
