import ProductL2Contraction_v1

/-! Literal partial integrals represent the already constructed L2 contractions. -/
noncomputable section
open MeasureTheory
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem slice_memLp_ae (F : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x => F (x,y)) 2 μ := by
  have hs := (Lp.memLp F).aestronglyMeasurable.prod_swap.prodMk_left
  have hi := ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_left_ae
  filter_upwards [hs,hi] with y hy hyi
  exact (memLp_two_iff_integrable_sq_norm hy).mpr hyi

theorem integral_inner_eq_L2 (f : Lp ℂ 2 μ) (h : X → ℂ) (hh : MemLp h 2 μ) :
    (∫ x, inner ℂ (f x) (h x) ∂μ) = inner ℂ f (hh.toLp h) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp] with x hx
  rw [hx]

theorem partialIntegral_norm_sq_bound (f : Lp ℂ 2 μ) (h : X → ℂ)
    (hh : MemLp h 2 μ) :
    ‖∫ x, inner ℂ (f x) (h x) ∂μ‖ ^ 2 ≤ ‖f‖ ^ 2 * ∫ x, ‖h x‖ ^ 2 ∂μ := by
  rw [integral_inner_eq_L2 f h hh]
  have hnorm : ‖hh.toLp h‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 ∂μ := by
    rw [norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with x hx
    rw [hx]
  calc
    ‖inner ℂ f (hh.toLp h)‖ ^ 2 ≤ (‖f‖ * ‖hh.toLp h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) _
    _ = ‖f‖ ^ 2 * ∫ x, ‖h x‖ ^ 2 ∂μ := by rw [mul_pow,hnorm]

def partialIntegralLeft (f : Lp ℂ 2 μ) (F : Lp ℂ 2 (μ.prod ν)) (y : Y) : ℂ :=
  ∫ x, inner ℂ (f x) (F (x,y)) ∂μ

theorem partialIntegralLeft_aestronglyMeasurable (f : Lp ℂ 2 μ)
    (F : Lp ℂ 2 (μ.prod ν)) : AEStronglyMeasurable (partialIntegralLeft f F) ν := by
  have hs : AEStronglyMeasurable (fun z : X × Y => inner ℂ (f z.1) (F z)) (μ.prod ν) :=
    (Lp.memLp f).aestronglyMeasurable.comp_fst.inner (Lp.memLp F).aestronglyMeasurable
  exact hs.prod_swap.integral_prod_right'

theorem partialIntegralLeft_memLp (f : Lp ℂ 2 μ) (F : Lp ℂ 2 (μ.prod ν)) :
    MemLp (partialIntegralLeft f F) 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm (partialIntegralLeft_aestronglyMeasurable f F)).mpr
  have hi := ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_right
  apply (hi.const_mul (‖f‖ ^ 2)).mono'
    ((partialIntegralLeft_aestronglyMeasurable f F).norm.pow 2)
  filter_upwards [slice_memLp_ae F] with y hy
  change ‖‖partialIntegralLeft f F y‖ ^ 2‖ ≤ ‖f‖ ^ 2 * ∫ x, ‖F (x,y)‖ ^ 2 ∂μ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖partialIntegralLeft f F y‖)]
  exact partialIntegral_norm_sq_bound f (fun x => F (x,y)) hy

def partialIntegralLeftL2 (f : Lp ℂ 2 μ) (F : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 ν :=
  (partialIntegralLeft_memLp f F).toLp (partialIntegralLeft f F)

#print axioms slice_memLp_ae
#print axioms partialIntegral_norm_sq_bound
#print axioms partialIntegralLeft_memLp
end TheoremT.ProductL2
