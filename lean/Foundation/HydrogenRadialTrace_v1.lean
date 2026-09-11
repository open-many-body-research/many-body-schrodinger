import HydrogenRadialLimits_v1

/-! Exact diagonal trace and one-electron Coulomb potential identities for the
actual radial derivative profiles. The trace is stated away from the nucleus. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem position_one_norm (x : Configuration 1) : ‖position x (0 : Fin 1)‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ k : Fin 3, (x (0,k))^2) = ∑ k : Fin 1 × Fin 3, (x k)^2
  rw [Fintype.sum_prod_type]
  simp

theorem coulombPotential_one_electron (Z : ℝ) (x : Configuration 1) :
    coulombPotential 1 Z x = -Z / ‖x‖ := by
  simp [coulombPotential, position_one_norm, div_eq_mul_inv, Finset.sum_filter]

theorem hydrogenSecond_trace (Z : ℝ) {x : Configuration 1} (hx : x ≠ 0) :
    (∑ k : Coordinate 1, hydrogenSecond Z k k x) =
      ((Z^2 - 2*Z/‖x‖ : ℝ) : ℂ) * hydrogenRadial Z x := by
  unfold hydrogenSecond
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 1
  congr 1
  have hnorm : (∑ k : Coordinate 1, (x k)^2) = ‖x‖^2 :=
    (EuclideanSpace.real_norm_sq_eq x).symm
  simp only [ite_true, mul_one, mul_assoc, ← pow_two,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, hnorm, nsmul_eq_mul]
  norm_num
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

#print axioms position_one_norm
#print axioms coulombPotential_one_electron
#print axioms hydrogenSecond_trace
end TheoremT.Continuum
