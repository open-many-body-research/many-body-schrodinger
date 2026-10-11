import WeightedFiniteCauchy_v1

/-! Pointwise coefficient bounds for the potential and its differentiated
forcing. The derivative coefficients are controlled by their sum of squares,
so the finite direction family contributes no additional cardinality factor.
The bound on that sum uses only the square of b1 and requires no sign for b1.
-/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem potential_smul_norm_sq_le (G : ℂ) {B b : ℝ} (hB : |B| ≤ b) :
    ‖B • G‖^2 ≤ b^2*‖G‖^2 := by
  rw [norm_smul,Real.norm_eq_abs,mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg B) hB 2) (sq_nonneg ‖G‖)

theorem potential_spectator_forcing_sum_norm_sq_le
    {ι : Type*} [Fintype ι] (A : ι → ℝ) (G : ℂ) (d : ι → ℂ)
    {B b b1 : ℝ} (hB : |B| ≤ b) (hA : (∑ j, |A j|^2) ≤ b1^2) :
    (∑ j, ‖-(A j • G) - B • d j‖^2) ≤
      2*b1^2*‖G‖^2 + 2*b^2*(∑ j, ‖d j‖^2) := by
  have hj (j : ι) : ‖-(A j • G) - B • d j‖^2 ≤
      2*|A j|^2*‖G‖^2 + 2*b^2*‖d j‖^2 := by
    have htwo := norm_add_sq_le_twice (-(A j • G)) (-(B • d j))
    have hbd := potential_smul_norm_sq_le (d j) hB
    simp only [norm_neg] at htwo
    have ha : ‖A j • G‖^2 = |A j|^2*‖G‖^2 := by
      rw [norm_smul,Real.norm_eq_abs,mul_pow]
    rw [ha] at htwo
    change ‖-(A j • G) + -(B • d j)‖^2 ≤ _
    nlinarith
  calc
    (∑ j, ‖-(A j • G) - B • d j‖^2)
      ≤ ∑ j, (2*|A j|^2*‖G‖^2 + 2*b^2*‖d j‖^2) :=
        Finset.sum_le_sum (fun j _ => hj j)
    _ = 2*(∑ j, |A j|^2)*‖G‖^2 + 2*b^2*(∑ j, ‖d j‖^2) := by
      simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
    _ ≤ 2*b1^2*‖G‖^2 + 2*b^2*(∑ j, ‖d j‖^2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2))
          (sq_nonneg ‖G‖)) le_rfl

#print axioms potential_smul_norm_sq_le
#print axioms potential_spectator_forcing_sum_norm_sq_le
end TheoremT.Continuum.WeakGrushin
