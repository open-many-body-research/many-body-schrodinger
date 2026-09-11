import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ComplexConjugate ContDiff InnerProductSpace
namespace TheoremT.HalfLineCompactHardy

abbrev halfLineMeasure : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
def quotient (f : ℝ → ℂ) (r : ℝ) : ℂ := r⁻¹ • f r

theorem quotient_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (quotient f) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r = 0
  · subst r
    have h0 : (0 : ℝ) ∉ tsupport f := fun h => (lt_irrefl (0 : ℝ)) (show (0 : ℝ) < 0 from hs h)
    have he := notMem_tsupport_iff_eventuallyEq.mp h0
    have heq : quotient f =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [he] with x hx
      simp [quotient, hx]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact (contDiffAt_id.inv hr).smul hf.contDiffAt

theorem quotient_compact {f : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (quotient f) := hc.smul_left (f := fun r : ℝ => r⁻¹)

theorem quotient_memLp {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    MemLp (quotient f) 2 halfLineMeasure :=
  (quotient_contDiff hf hs).continuous.memLp_of_hasCompactSupport (quotient_compact hc)

theorem deriv_memLp {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : MemLp (deriv f) 2 halfLineMeasure :=
  (hf.continuous_deriv (by simp)).memLp_of_hasCompactSupport hc.deriv

def primitive (f : ℝ → ℂ) (r : ℝ) : ℝ := r * ‖quotient f r‖^2

theorem primitive_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (primitive f) :=
  contDiff_id.mul ((quotient_contDiff hf hs).norm_sq ℂ)

theorem primitive_compact {f : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (primitive f) := by
  unfold primitive
  simp only [pow_two]
  exact ((quotient_compact hc).norm.mul_left (f := fun r => ‖quotient f r‖)).mul_left
    (f := fun r => r)

theorem primitive_deriv_pos {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {r : ℝ} (hr : 0 < r) :
    deriv (primitive f) r =
      2 * ⟪quotient f r, deriv f r⟫_ℝ - ‖quotient f r‖^2 := by
  have hd := (hf.differentiable (by simp) r).hasDerivAt
  have hq := ((hasDerivAt_id r).inv hr.ne').smul hd
  have hp := (hasDerivAt_id r).mul hq.norm_sq
  change HasDerivAt (primitive f) _ r at hp
  rw [hp.deriv]
  change 1 * ‖r⁻¹ • f r‖^2 + r * (2 * ⟪r⁻¹ • f r,
    r⁻¹ • deriv f r + (-1 / r^2) • f r⟫_ℝ) = _
  simp only [quotient, one_mul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hr, real_inner_smul_left, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, smul_smul]
  field_simp
  <;> ring

theorem compact_hardy_identity {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ r, ‖quotient f r‖^2 ∂halfLineMeasure) =
      2 * ∫ r, ⟪quotient f r, deriv f r⟫_ℝ ∂halfLineMeasure := by
  have hq := quotient_memLp hf hc hs
  have hd := deriv_memLp hf hc
  have hiq := hq.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hid : Integrable (fun r => ⟪quotient f r, deriv f r⟫_ℝ) halfLineMeasure :=
    (L2.integrable_inner (𝕜 := ℝ) (hq.toLp _) (hd.toLp _)).congr (by
      filter_upwards [hq.coeFn_toLp, hd.coeFn_toLp] with r hqr hdr
      rw [hqr, hdr])
  have hz := (primitive_compact hc).integral_Ioi_deriv_eq
    ((primitive_contDiff hf hs).of_le (by simp)) 0
  have he : (∫ r, deriv (primitive f) r ∂halfLineMeasure) =
      2 * ∫ r, ⟪quotient f r, deriv f r⟫_ℝ ∂halfLineMeasure -
        ∫ r, ‖quotient f r‖^2 ∂halfLineMeasure := by
    calc
      _ = ∫ r, (2 * ⟪quotient f r, deriv f r⟫_ℝ - ‖quotient f r‖^2)
          ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact primitive_deriv_pos hf hr
      _ = _ := by rw [integral_sub (hid.const_mul 2) hiq, integral_const_mul]
  simp only [primitive, zero_mul, neg_zero] at hz
  change (∫ r, deriv (primitive f) r ∂halfLineMeasure) = 0 at hz
  linarith

#print axioms compact_hardy_identity
end TheoremT.HalfLineCompactHardy
