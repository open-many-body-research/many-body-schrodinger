import ProductL2PartialIntegralIdentity_v1

/-! The second-coordinate contraction also has the literal Fubini representative. -/
noncomputable section
open MeasureTheory
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem slice_memLp_right_ae (F : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => F (x,y)) 2 ν := by
  have hs := (Lp.memLp F).aestronglyMeasurable.prodMk_left
  have hi := ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae
  filter_upwards [hs,hi] with x hx hxi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hxi

def partialIntegralRight (g : Lp ℂ 2 ν) (F : Lp ℂ 2 (μ.prod ν)) (x : X) : ℂ :=
  ∫ y, inner ℂ (g y) (F (x,y)) ∂ν

theorem partialIntegralRight_aestronglyMeasurable (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) : AEStronglyMeasurable (partialIntegralRight g F) μ := by
  have hs : AEStronglyMeasurable (fun z : X × Y => inner ℂ (g z.2) (F z)) (μ.prod ν) :=
    (Lp.memLp g).aestronglyMeasurable.comp_snd.inner (Lp.memLp F).aestronglyMeasurable
  exact hs.integral_prod_right'

theorem partialIntegralRight_memLp (g : Lp ℂ 2 ν) (F : Lp ℂ 2 (μ.prod ν)) :
    MemLp (partialIntegralRight g F) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (partialIntegralRight_aestronglyMeasurable g F)).mpr
  have hi := ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
  apply (hi.const_mul (‖g‖ ^ 2)).mono'
    ((partialIntegralRight_aestronglyMeasurable g F).norm.pow 2)
  filter_upwards [slice_memLp_right_ae F] with x hx
  change ‖‖partialIntegralRight g F x‖ ^ 2‖ ≤ ‖g‖ ^ 2 * ∫ y, ‖F (x,y)‖ ^ 2 ∂ν
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖partialIntegralRight g F x‖)]
  exact partialIntegral_norm_sq_bound g (fun y => F (x,y)) hx

def partialIntegralRightL2 (g : Lp ℂ 2 ν) (F : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 μ :=
  (partialIntegralRight_memLp g F).toLp (partialIntegralRight g F)

theorem partialIntegralRightL2_pairing (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) :
    inner ℂ f (partialIntegralRightL2 g F) = inner ℂ (tensor f g) F := by
  have he : (fun z : X × Y => inner ℂ (tensor f g z) (F z)) =ᵐ[μ.prod ν]
      fun z => inner ℂ (f z.1 * g z.2) (F z) := by
    filter_upwards [tensor_ae f g] with z hz
    rw [hz]
  have hi : Integrable (fun z : X × Y => inner ℂ (f z.1 * g z.2) (F z)) (μ.prod ν) :=
    (L2.integrable_inner (𝕜 := ℂ) (tensor f g) F).congr he
  rw [L2.inner_def,L2.inner_def]
  calc
    (∫ x, inner ℂ (f x) (partialIntegralRightL2 g F x) ∂μ) =
        ∫ x, inner ℂ (f x) (partialIntegralRight g F x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [(partialIntegralRight_memLp g F).coeFn_toLp] with x hx
      rw [show partialIntegralRightL2 g F x = partialIntegralRight g F x from hx]
    _ = ∫ x, ∫ y, inner ℂ (f x * g y) (F (x,y)) ∂ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change inner ℂ (f x) (partialIntegralRight g F x) =
          ∫ y, inner ℂ (f x * g y) (F (x,y)) ∂ν
        rw [RCLike.inner_apply,partialIntegralRight,← integral_mul_const]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [RCLike.inner_apply,map_mul]
          ring
    _ = ∫ z : X × Y, inner ℂ (f z.1 * g z.2) (F z) ∂μ.prod ν :=
      (integral_prod _ hi).symm
    _ = ∫ z, inner ℂ (tensor f g z) (F z) ∂μ.prod ν := integral_congr_ae he.symm

theorem contractRight_eq_partialIntegralRightL2 (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) : contractRight g F = partialIntegralRightL2 g F := by
  apply ext_inner_left ℂ
  intro f
  rw [contractRight_pairing,partialIntegralRightL2_pairing]

theorem contractRight_ae_partialIntegral (g : Lp ℂ 2 ν) (F : Lp ℂ 2 (μ.prod ν)) :
    contractRight g F =ᵐ[μ] fun x => ∫ y, inner ℂ (g y) (F (x,y)) ∂ν := by
  rw [contractRight_eq_partialIntegralRightL2]
  exact (partialIntegralRight_memLp g F).coeFn_toLp

#print axioms partialIntegralRight_memLp
#print axioms partialIntegralRightL2_pairing
#print axioms contractRight_ae_partialIntegral
end TheoremT.ProductL2
