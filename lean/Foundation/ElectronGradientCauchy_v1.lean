import WeakCoulombNorm_v2

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem sum_electron_derivative_norm_le {N : ℕ} (d : Coordinate N → SpatialL2 N) :
    (∑ i : Fin N, Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2)) ≤
      Real.sqrt (N : ℝ) * Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin N))
    (f := fun _ => (1 : ℝ)) (g := fun i => ∑ k : Fin 3, ‖d (i,k)‖^2)
    (fun _ => by norm_num) (fun i => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [Fintype.sum_prod_type]
  simpa only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using h

theorem coulomb_directional_coefficient_nonneg (N : ℕ) (Z : ℝ) :
    0 ≤ Real.sqrt (N : ℝ) * (2*|Z| + (N : ℝ) - 1) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith [abs_nonneg Z])

theorem weighted_sum_electron_derivative_norm_le {N : ℕ} (Z : ℝ)
    (d : Coordinate N → SpatialL2 N) :
    (2*|Z| + (N : ℝ) - 1) * (∑ i : Fin N, Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2)) ≤
      (Real.sqrt (N : ℝ) * (2*|Z| + (N : ℝ) - 1)) *
        Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    have hP : 0 ≤ 2*|Z| + (N : ℝ) - 1 := by linarith [abs_nonneg Z]
    exact (mul_le_mul_of_nonneg_left (sum_electron_derivative_norm_le d) hP).trans_eq (by ring)

#print axioms sum_electron_derivative_norm_le
#print axioms weighted_sum_electron_derivative_norm_le
end TheoremT.Continuum
