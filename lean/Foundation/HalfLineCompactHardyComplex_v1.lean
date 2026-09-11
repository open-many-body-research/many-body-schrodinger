import HalfLineCompactHardyNorm_v1

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ComplexConjugate ContDiff InnerProductSpace
namespace TheoremT.HalfLineCompactHardy

theorem compact_hardy_cross_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    Integrable (fun r => conj (f r) * deriv f r / (r : ℂ)) halfLineMeasure := by
  have hq := quotient_memLp hf hc hs
  have hd := deriv_memLp hf hc
  apply (L2.integrable_inner (𝕜 := ℂ) (hq.toLp _) (hd.toLp _)).congr
  filter_upwards [hq.coeFn_toLp, hd.coeFn_toLp] with r hqr hdr
  rw [hqr, hdr, quotient_eq_div]
  simp only [RCLike.inner_apply, map_div₀, map_mul, map_inv₀, Complex.conj_ofReal, div_eq_mul_inv]
  ring

theorem compact_hardy_identity_re_integral {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ r, ‖f r‖^2 / r^2 ∂halfLineMeasure) =
      2 * (∫ r, conj (f r) * deriv f r / (r : ℂ) ∂halfLineMeasure).re := by
  rw [compact_hardy_complex_identity hf hc hs]
  congr 1
  exact integral_re (compact_hardy_cross_integrable hf hc hs)

#print axioms compact_hardy_cross_integrable
#print axioms compact_hardy_identity_re_integral
end TheoremT.HalfLineCompactHardy
