import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace TheoremT.Continuum
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure X}

theorem actual_l2_toLp_norm_sq_integral {f : X → F} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq]

theorem actual_l2_integral_inner_abs_le {f g : X → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤ ‖hf.toLp f‖*‖hg.toLp g‖ := by
  have he : inner ℝ (hf.toLp f) (hg.toLp g)=∫ x, inner ℝ (f x) (g x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    rw [hx,hy]
  rw [← he]
  exact abs_real_inner_le_norm _ _

theorem actual_l2_integral_inner_sq_le {f g : X → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ)^2 ≤ (∫ x, ‖f x‖^2 ∂μ)*(∫ x, ‖g x‖^2 ∂μ) := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (actual_l2_integral_inner_abs_le hf hg) 2
  simpa only [sq_abs,mul_pow,actual_l2_toLp_norm_sq_integral] using h

#print axioms actual_l2_toLp_norm_sq_integral
#print axioms actual_l2_integral_inner_abs_le
#print axioms actual_l2_integral_inner_sq_le
end TheoremT.Continuum
