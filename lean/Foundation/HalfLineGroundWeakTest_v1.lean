import HalfLineWeakODE_v1
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The explicit radial ground profile satisfies the partner weak equation
against every actual complex smooth compact test in the positive half-line. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.OneDimensional

theorem radialGround_hasDerivAt (Z x : ℝ) :
    HasDerivAt (fun y : ℝ => y*Real.exp (-Z*y))
      ((1-Z*x)*Real.exp (-Z*x)) x := by
  have h := (hasDerivAt_id' x).fun_mul (((hasDerivAt_id' x).const_mul (-Z)).exp)
  exact h.congr_deriv (by ring)

theorem radialGround_weak_test (Z : ℝ) (ψ : ℝ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    ∫ x, (-deriv ψ x-x⁻¹ • ψ x+Z • ψ x) *
      ((x*Real.exp (-Z*x) : ℝ) : ℂ) = 0 := by
  let g : ℝ → ℂ := fun x => ((x*Real.exp (-Z*x) : ℝ) : ℂ)
  let dg : ℝ → ℂ := fun x => (((1-Z*x)*Real.exp (-Z*x) : ℝ) : ℂ)
  have hg : ∀ x, HasDerivAt g (dg x) x := fun x => (radialGround_hasDerivAt Z x).ofReal_comp
  have hgc : Continuous g := Complex.continuous_ofReal.comp
    (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  have hdgc : Continuous dg := Complex.continuous_ofReal.comp
    ((continuous_const.sub (continuous_const.mul continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  have hψdc := hψ.continuous_deriv (by simp)
  have hi : Integrable (fun x => deriv ψ x*g x+ψ x*dg x) :=
    ((hψdc.mul hgc).integrable_of_hasCompactSupport hc.deriv.mul_right).add
      ((hψ.continuous.mul hdgc).integrable_of_hasCompactSupport hc.mul_right)
  have hp : Integrable (fun x => ψ x*g x) :=
    (hψ.continuous.mul hgc).integrable_of_hasCompactSupport hc.mul_right
  have hz : ∫ x, deriv ψ x*g x+ψ x*dg x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun x => (hψ.differentiable (by simp) x).hasDerivAt.fun_mul (hg x)) hi hp
  have he : (fun x => (-deriv ψ x-x⁻¹ • ψ x+Z • ψ x)*g x) =
      fun x => -(deriv ψ x*g x+ψ x*dg x) := by
    funext x
    by_cases hx : x = 0
    · subst x
      have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport (by
        intro h
        exact (lt_irrefl (0 : ℝ)) (hs h))
      simp [g,dg,hψ0]
    · simp only [g,dg,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,
        Complex.ofReal_one,Complex.ofReal_inv]
      have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      field_simp
      <;> ring
  change (∫ x, (-deriv ψ x-x⁻¹ • ψ x+Z • ψ x)*g x) = 0
  rw [he,integral_neg,hz,neg_zero]

#print axioms radialGround_hasDerivAt
#print axioms radialGround_weak_test
end TheoremT.OneDimensional
