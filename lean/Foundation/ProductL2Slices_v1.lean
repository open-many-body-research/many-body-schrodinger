import ProductL2PartialIntegralRight_v1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Actual L2 slices and their squared norm as an integrable function.
The default value outside the proved almost-everywhere L2 slice set is zero. -/
noncomputable section
open MeasureTheory
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def sliceLeft (F : Lp ℂ 2 (μ.prod ν)) (y : Y) : Lp ℂ 2 μ := by
  classical
  exact if h : MemLp (fun x => F (x,y)) 2 μ then h.toLp (fun x => F (x,y)) else 0

theorem sliceLeft_ae_coe (F : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, sliceLeft F y =ᵐ[μ] fun x => F (x,y) := by
  filter_upwards [slice_memLp_ae F] with y hy
  simp only [sliceLeft,dite_eq_left hy]
  exact hy.coeFn_toLp

def sliceNormSq (F : Lp ℂ 2 (μ.prod ν)) (y : Y) : ℝ :=
  ∫ x, ‖F (x,y)‖ ^ 2 ∂μ

theorem sliceNormSq_nonneg (F : Lp ℂ 2 (μ.prod ν)) (y : Y) :
    0 ≤ sliceNormSq F y := integral_nonneg (fun _ => sq_nonneg _)

theorem sliceNormSq_integrable (F : Lp ℂ 2 (μ.prod ν)) :
    Integrable (sliceNormSq F) ν :=
  ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_right

theorem sliceNormSq_integral (F : Lp ℂ 2 (μ.prod ν)) :
    (∫ y, sliceNormSq F y ∂ν) = ‖F‖ ^ 2 := by
  rw [norm_sq_integral]
  exact (integral_prod_symm _
    ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).symm

theorem sliceLeft_norm_sq_ae (F : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, ‖sliceLeft F y‖ ^ 2 = sliceNormSq F y := by
  filter_upwards [sliceLeft_ae_coe F] with y hy
  rw [norm_sq_integral]
  exact integral_congr_ae (hy.fun_comp (fun z : ℂ => ‖z‖ ^ 2))

theorem sliceLeft_sub_ae (F G : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, sliceLeft (F-G) y = sliceLeft F y - sliceLeft G y := by
  have hs := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae
    (Lp.coeFn_sub F G)
  filter_upwards [sliceLeft_ae_coe (F-G),sliceLeft_ae_coe F,sliceLeft_ae_coe G,
    Measure.ae_ae_of_ae_prod hs] with y hFG hF hG hsub
  apply Lp.ext
  filter_upwards [hFG,hF,hG,hsub,Lp.coeFn_sub (sliceLeft F y) (sliceLeft G y)]
    with x hx hxF hxG hxsub hxs
  simp only [Pi.sub_apply] at hxsub hxs
  rw [hx,hxs,hxF,hxG]
  exact hxsub

theorem sliceLeft_dist_sq_ae (F G : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, dist (sliceLeft F y) (sliceLeft G y) ^ 2 = sliceNormSq (F-G) y := by
  filter_upwards [sliceLeft_sub_ae F G,sliceLeft_norm_sq_ae (F-G)] with y hsub hn
  rw [dist_eq_norm,← hsub,hn]

#print axioms sliceLeft_ae_coe
#print axioms sliceNormSq_integral
#print axioms sliceLeft_dist_sq_ae
end TheoremT.ProductL2
