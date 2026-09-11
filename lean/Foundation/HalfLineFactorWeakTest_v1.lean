import HalfLineFactors_v1
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Real compact tests turn orthogonality to the actual partner range into
the weak hydrogen ODE, with the declared half-line measure. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.HalfLine

theorem B_coe (Z : ℝ) (u : D) : (B Z u : ℝ → ℂ) =ᵐ[μ]
    fun x => -dJ u x - x⁻¹ • J u x + Z • J u x := by
  rw [B_apply]
  filter_upwards [Lp.coeFn_add (-dJ u - W u) (Z • J u),
    Lp.coeFn_sub (-dJ u) (W u), Lp.coeFn_neg (dJ u),
    Lp.coeFn_smul Z (J u), W_coe u] with x ha hs hn hz hw
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply] at ha hs hn hz
  rw [ha, hs, hn, hz, hw]

theorem Test.ofReal_deriv (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) (x : ℝ) :
    deriv (Test.ofReal φ hφ hc hs : ℝ → ℂ) x = ((deriv φ x : ℝ) : ℂ) :=
  (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
    (hφ.differentiable (by simp) x).hasDerivAt).deriv

theorem B_real_test_coe (Z : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) :
    (B Z (testEmbed (Test.ofReal φ hφ hc hs)) : ℝ → ℂ) =ᵐ[μ]
      fun x => ((-deriv φ x - φ x / x + Z * φ x : ℝ) : ℂ) := by
  let t := Test.ofReal φ hφ hc hs
  have hb := B_coe Z (testEmbed t)
  simp only [dJ_testEmbed, J_testEmbed] at hb
  filter_upwards [hb, t.coe_value, t.coe_gradient] with x hx hv hd
  rw [hx, hv, hd, Test.ofReal_deriv]
  simp [t, Test.ofReal, Function.comp_apply, Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem range_orthogonal_real_test {Z : ℝ} {f : E} (hf : f ∈ (B Z).range.orthogonal)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) :
    (∫ x, (-deriv φ x - φ x / x + Z * φ x) • f x ∂μ) = 0 := by
  have he := hf (B Z (testEmbed (Test.ofReal φ hφ hc hs)))
    (LinearMap.mem_range_self (B Z).toLinearMap (testEmbed (Test.ofReal φ hφ hc hs)))
  rw [L2.inner_def] at he
  have hi : (∫ x, inner ℂ (B Z (testEmbed (Test.ofReal φ hφ hc hs)) x) (f x) ∂μ) =
      ∫ x, (-deriv φ x - φ x / x + Z * φ x) • f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [B_real_test_coe Z φ hφ hc hs] with x hx
    rw [hx]
    simp [RCLike.inner_apply, Complex.real_smul, mul_comm]
  rw [hi] at he
  exact he

#print axioms B_coe
#print axioms B_real_test_coe
#print axioms range_orthogonal_real_test
end TheoremT.HalfLine
