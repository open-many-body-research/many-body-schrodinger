import HalfLineCompactHardy_v1

/-! One-dimensional compact Hardy, as an actual L² norm inequality.
The integral identity is proved from compact integration by parts in the
imported source; no Hardy bound or zero-trace closure is a hypothesis. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ComplexConjugate ContDiff InnerProductSpace
namespace TheoremT.HalfLineCompactHardy

theorem toLp_norm_sq_integral {f : ℝ → ℂ} (h : MemLp f 2 halfLineMeasure) :
    ‖h.toLp f‖^2 = ∫ r, ‖f r‖^2 ∂halfLineMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with r hr
  rw [hr]

theorem toLp_real_inner_integral {f g : ℝ → ℂ}
    (hf : MemLp f 2 halfLineMeasure) (hg : MemLp g 2 halfLineMeasure) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ r, ⟪f r, g r⟫_ℝ ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with r hfr hgr
  rw [hfr, hgr]

theorem compact_hardy_toLp_norm {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hq : MemLp (quotient f) 2 halfLineMeasure)
    (hd : MemLp (deriv f) 2 halfLineMeasure) :
    ‖hq.toLp (quotient f)‖ ≤ 2 * ‖hd.toLp (deriv f)‖ := by
  have he := compact_hardy_identity hf hc hs
  rw [← toLp_norm_sq_integral hq, ← toLp_real_inner_integral hq hd] at he
  have hi := real_inner_le_norm (hq.toLp (quotient f)) (hd.toLp (deriv f))
  by_cases hz : ‖hq.toLp (quotient f)‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖hq.toLp (quotient f)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

theorem compact_hardy_eLpNorm {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    (eLpNorm (quotient f) 2 halfLineMeasure).toReal ≤
      2 * (eLpNorm (deriv f) 2 halfLineMeasure).toReal := by
  simpa only [Lp.norm_toLp] using compact_hardy_toLp_norm hf hc hs
    (quotient_memLp hf hc hs) (deriv_memLp hf hc)

theorem compact_hardy_integral_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ r, ‖quotient f r‖^2 ∂halfLineMeasure) ≤
      4 * ∫ r, ‖deriv f r‖^2 ∂halfLineMeasure := by
  have hq := quotient_memLp hf hc hs
  have hd := deriv_memLp hf hc
  rw [← toLp_norm_sq_integral hq, ← toLp_norm_sq_integral hd]
  have h := compact_hardy_toLp_norm hf hc hs hq hd
  nlinarith [norm_nonneg (hq.toLp (quotient f)), norm_nonneg (hd.toLp (deriv f))]

theorem quotient_eq_div (f : ℝ → ℂ) (r : ℝ) :
    quotient f r = f r / (r : ℂ) := by
  simp [quotient, Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem compact_hardy_complex_identity {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ r, ‖f r‖^2 / r^2 ∂halfLineMeasure) =
      2 * ∫ r, (conj (f r) * deriv f r / (r : ℂ)).re ∂halfLineMeasure := by
  have he := compact_hardy_identity hf hc hs
  convert he using 1
  · apply integral_congr_ae
    exact ae_of_all _ fun r => by
      change ‖f r‖^2 / r^2 = ‖quotient f r‖^2
      rw [quotient_eq_div, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  · congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun r => by
      simp [quotient, real_inner_smul_left, Complex.inner, Complex.mul_re,
        Complex.div_ofReal_re, div_eq_mul_inv]
      ring

#print axioms compact_hardy_toLp_norm
#print axioms compact_hardy_eLpNorm
#print axioms compact_hardy_integral_bound
#print axioms compact_hardy_complex_identity
end TheoremT.HalfLineCompactHardy
