import ProductL2PartialIntegral_v1

/-! Fubini identifies the genuine partial integral with the bounded Hilbert adjoint. -/
noncomputable section
open MeasureTheory
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem partialIntegralLeftL2_pairing (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) :
    inner ℂ g (partialIntegralLeftL2 f F) = inner ℂ (tensor f g) F := by
  have he : (fun z : X × Y => inner ℂ (tensor f g z) (F z)) =ᵐ[μ.prod ν]
      fun z => inner ℂ (f z.1 * g z.2) (F z) := by
    filter_upwards [tensor_ae f g] with z hz
    rw [hz]
  have hi : Integrable (fun z : X × Y => inner ℂ (f z.1 * g z.2) (F z)) (μ.prod ν) :=
    (L2.integrable_inner (𝕜 := ℂ) (tensor f g) F).congr he
  rw [L2.inner_def,L2.inner_def]
  calc
    (∫ y, inner ℂ (g y) (partialIntegralLeftL2 f F y) ∂ν) =
        ∫ y, inner ℂ (g y) (partialIntegralLeft f F y) ∂ν := by
      apply integral_congr_ae
      filter_upwards [(partialIntegralLeft_memLp f F).coeFn_toLp] with y hy
      rw [show partialIntegralLeftL2 f F y = partialIntegralLeft f F y from hy]
    _ = ∫ y, ∫ x, inner ℂ (f x * g y) (F (x,y)) ∂μ ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change inner ℂ (g y) (partialIntegralLeft f F y) =
          ∫ x, inner ℂ (f x * g y) (F (x,y)) ∂μ
        rw [RCLike.inner_apply,partialIntegralLeft,← integral_mul_const]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [RCLike.inner_apply,map_mul]
          ring
    _ = ∫ z : X × Y, inner ℂ (f z.1 * g z.2) (F z) ∂μ.prod ν :=
      (integral_prod_symm _ hi).symm
    _ = ∫ z, inner ℂ (tensor f g z) (F z) ∂μ.prod ν := integral_congr_ae he.symm

theorem contractLeft_eq_partialIntegralLeftL2 (f : Lp ℂ 2 μ)
    (F : Lp ℂ 2 (μ.prod ν)) : contractLeft f F = partialIntegralLeftL2 f F := by
  apply ext_inner_left ℂ
  intro g
  rw [contractLeft_pairing,partialIntegralLeftL2_pairing]

theorem contractLeft_ae_partialIntegral (f : Lp ℂ 2 μ) (F : Lp ℂ 2 (μ.prod ν)) :
    contractLeft f F =ᵐ[ν] fun y => ∫ x, inner ℂ (f x) (F (x,y)) ∂μ := by
  rw [contractLeft_eq_partialIntegralLeftL2]
  exact (partialIntegralLeft_memLp f F).coeFn_toLp

#print axioms partialIntegralLeftL2_pairing
#print axioms contractLeft_eq_partialIntegralLeftL2
#print axioms contractLeft_ae_partialIntegral
end TheoremT.ProductL2
