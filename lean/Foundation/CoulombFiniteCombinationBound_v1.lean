import CoulombCuspRegularizationError_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem coulomb_finite_combination_abs_bound (N : ℕ) (Z : ℝ)
    (a α : Fin N → ℝ) (b β : Fin N → Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ α i) (hb : ∀ i j, i<j → |b i j| ≤ β i j) :
    |-Z*(∑ i, a i)+(1/2:ℝ)*(∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j), b i j)| ≤
      |Z| * (∑ i, α i)+(1/2:ℝ)*(∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j), β i j) := by
  have hn : |∑ i, a i| ≤ ∑ i, α i :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ha i))
  have hp : |∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j), b i j| ≤
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j), β i j := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun j hj => hb i j (Finset.mem_filter.mp hj).2)
  have h := abs_add_le (-Z*(∑ i, a i))
    ((1/2:ℝ)*(∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j), b i j))
  simp only [abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hn (abs_nonneg Z))
    (mul_le_mul_of_nonneg_left hp (by norm_num)))

#print axioms coulomb_finite_combination_abs_bound
end TheoremT.Continuum
