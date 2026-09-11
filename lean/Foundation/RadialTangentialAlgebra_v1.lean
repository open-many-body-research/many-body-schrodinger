import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Exact radial/tangential decomposition for real-linear maps with a Hilbert
codomain, including complex-valued physical derivatives. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Polar
variable {ι F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem weighted_vector_residuals (a : ι → F) (c : ι → ℝ)
    (hc : ∑ i, (c i)^2 = 1) :
    (∑ i, ‖a i-c i • (∑ j, c j • a j)‖^2) +
      ‖∑ j, c j • a j‖^2 = ∑ i, ‖a i‖^2 := by
  let b := ∑ j, c j • a j
  have hi : (∑ i, c i * inner ℝ (a i) b) = ‖b‖^2 := by
    calc
      (∑ i, c i * inner ℝ (a i) b) = inner ℝ (∑ i, c i • a i) b := by
        simp only [sum_inner,real_inner_smul_left]
      _ = ‖b‖^2 := real_inner_self_eq_norm_sq b
  change (∑ i, ‖a i-c i • b‖^2)+‖b‖^2 = _
  simp_rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hcross : (∑ i, 2 * (c i * inner ℝ (a i) b)) = 2*‖b‖^2 := by
    rw [← Finset.mul_sum,hi]
  have hlast : (∑ i, (c i)^2 * ‖b‖^2) = ‖b‖^2 := by
    rw [← Finset.sum_mul,hc,one_mul]
  rw [hcross,hlast]
  ring

theorem euclidean_unit_direction_decomposition [DecidableEq ι]
    (L : EuclideanSpace ℝ ι →L[ℝ] F) (w : EuclideanSpace ℝ ι) (hw : ‖w‖ = 1) :
    (∑ i, ‖L (EuclideanSpace.single i 1)‖^2) =
      ‖L w‖^2 + ∑ i, ‖L (EuclideanSpace.single i 1)-w i • L w‖^2 := by
  have hw2 : ∑ i, (w i)^2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq,hw,one_pow]
  have hrepr : ∑ i, w i • EuclideanSpace.single i (1:ℝ) = w := by
    simpa only [EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun ι ℝ).sum_repr w
  have hL : (∑ i, w i • L (EuclideanSpace.single i 1)) = L w := by
    simp_rw [← map_smul]
    rw [← map_sum,hrepr]
  have h := weighted_vector_residuals (fun i => L (EuclideanSpace.single i 1))
    (fun i => w i) hw2
  rw [hL] at h
  linarith

#print axioms weighted_vector_residuals
#print axioms euclidean_unit_direction_decomposition
end TheoremT.Polar
