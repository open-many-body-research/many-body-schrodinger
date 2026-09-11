import WeakGrushinCutoffAlgebra_v1

/-! Weighted finite Cauchy inequality for vectors in any real normed space.
Nonnegative weights may vanish; no dimension factor or inner-product structure
on the vector codomain is required. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
variable {I F : Type*} [Fintype I] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_weighted_cauchy_sq (w a : I → ℝ) (z : I → F)
    (hw : ∀ i, 0 ≤ w i) :
    ‖∑ i, (w i*a i) • z i‖^2 ≤
      (∑ i, w i*(a i)^2)*(∑ i, w i*‖z i‖^2) := by
  have hn : ‖∑ i, (w i*a i) • z i‖ ≤ ∑ i, w i*|a i| *‖z i‖ := by
    calc
      _ ≤ ∑ i, ‖(w i*a i) • z i‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw i)]
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => w i*|a i| *‖z i‖)
    (f := fun i => w i*(a i)^2) (g := fun i => w i*‖z i‖^2)
    (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    (fun i _ => le_of_eq (by simp only [mul_pow,sq_abs]; ring))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

theorem norm_add_sq_le_twice (x y : F) :
    ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (x+y)) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

#print axioms finite_weighted_cauchy_sq
#print axioms norm_add_sq_le_twice
end TheoremT.Continuum
