import HalfLineDerivativeUnique_v1
import HalfLineCompactHardyComplex_v1

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ComplexConjugate ContDiff InnerProductSpace
namespace TheoremT.HalfLine
open HalfLineCompactHardy

def Test.quotientLp (f : Test) : E :=
  (quotient_memLp f.smooth f.compact f.support).toLp (quotient f)

theorem Test.coe_quotientLp (f : Test) :
    (f.quotientLp : ℝ → ℂ) =ᵐ[μ] quotient f :=
  (quotient_memLp f.smooth f.compact f.support).coeFn_toLp

theorem Test.quotient_bound (f : Test) : ‖f.quotientLp‖ ≤ 2 * ‖f.gradient‖ :=
  compact_hardy_toLp_norm f.smooth f.compact f.support
    (quotient_memLp f.smooth f.compact f.support) f.deriv_memLp

theorem Test.value_gradient_re_zero (f : Test) :
    (inner ℂ f.value f.gradient).re = 0 := by
  have hi := congrArg Complex.re (f.pair_ibp f)
  simp only [Complex.neg_re] at hi
  have hs := inner_re_symm (𝕜 := ℂ) f.value f.gradient
  change (inner ℂ f.value f.gradient).re = (inner ℂ f.gradient f.value).re at hs
  linarith

theorem l2_real_inner_eq_re_complex (f g : E) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ r, (inner ℂ (f r) (g r)).re ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun r => by simp only [Complex.inner, RCLike.inner_apply]
    _ = _ := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

theorem Test.value_gradient_real_zero (f : Test) :
    inner ℝ f.value f.gradient = 0 := by
  rw [l2_real_inner_eq_re_complex, f.value_gradient_re_zero]

theorem Test.quotient_gradient_real (f : Test) :
    2 * inner ℝ f.quotientLp f.gradient = ‖f.quotientLp‖^2 := by
  have he := compact_hardy_identity f.smooth f.compact f.support
  rw [← toLp_norm_sq_integral (quotient_memLp f.smooth f.compact f.support),
    ← toLp_real_inner_integral (quotient_memLp f.smooth f.compact f.support)
      f.deriv_memLp] at he
  exact he.symm

theorem Test.quotient_gradient_re (f : Test) :
    2 * (inner ℂ f.quotientLp f.gradient).re = ‖f.quotientLp‖^2 := by
  simpa only [l2_real_inner_eq_re_complex] using f.quotient_gradient_real

theorem Test.quotient_pair_symmetry (f g : Test) :
    inner ℂ f.quotientLp g.value = inner ℂ f.value g.quotientLp := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coe_quotientLp, g.coe_value, f.coe_value, g.coe_quotientLp]
    with r hfq hgv hfv hgq
  rw [hfq, hgv, hfv, hgq]
  simp only [quotient_eq_div, RCLike.inner_apply, map_div₀, Complex.conj_ofReal,
    div_eq_mul_inv, map_mul, map_inv₀]
  ring

theorem Test.quotient_value_real (f : Test) :
    inner ℝ f.quotientLp f.value = ∫ r, ‖f r‖^2 / r ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coe_quotientLp, f.coe_value] with r hfq hfv
  rw [hfq, hfv]
  simp only [quotient, real_inner_smul_left, real_inner_self_eq_norm_sq, div_eq_mul_inv]
  ring

#print axioms Test.quotient_bound
#print axioms Test.value_gradient_real_zero
#print axioms Test.quotient_gradient_real
#print axioms Test.quotient_pair_symmetry
#print axioms Test.quotient_value_real
end TheoremT.HalfLine
