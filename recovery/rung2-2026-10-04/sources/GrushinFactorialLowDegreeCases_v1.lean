import GrushinFactorialIndexDecomposition_v1

/-! Exact coordinate classification for multiindices of total degree at most two.
The two degree-one summands may have the same index, so repeated derivatives
are included. No derivative compatibility is presumed here. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem finite_multiindex_eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι]
    (α : ι → ℕ) (h : (∑ i, α i) = 0) : α = 0 := by
  funext i
  exact Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i)

theorem finite_multiindex_single_of_sum_eq_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] (α : ι → ℕ) (h : (∑ i, α i) = 1) :
    ∃ i, α = Pi.single i 1 := by
  let f : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm α
  have hf : f.degree = 1 := by
    rw [Finsupp.degree_eq_sum]
    exact h
  have hm : f ∈ Set.range (fun i : ι => Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact hf
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, ?_⟩
  funext j
  have hj := congrArg (fun g : ι →₀ ℕ => g j) hi
  simpa [f, Finsupp.single_apply, Pi.single_apply, eq_comm] using hj.symm

theorem finite_multiindex_two_singles_of_sum_eq_two {ι : Type*}
    [Fintype ι] [DecidableEq ι] (α : ι → ℕ) (h : (∑ i, α i) = 2) :
    ∃ i j, α = Pi.single i 1 + Pi.single j 1 := by
  obtain ⟨η, hη, hs⟩ := finite_submultiindex_degree α 1 (by omega)
  obtain ⟨i, hi⟩ := finite_multiindex_single_of_sum_eq_one η hs
  have hr : (∑ l, (α l - η l)) = 1 := by
    rw [Finset.sum_tsub_distrib _ (fun l _ => hη l), h, hs]
  obtain ⟨j, hj⟩ := finite_multiindex_single_of_sum_eq_one (fun l => α l - η l) hr
  refine ⟨i, j, ?_⟩
  rw [← hi, ← hj]
  funext l
  exact (Nat.add_sub_of_le (hη l)).symm

theorem finite_multiindex_degree_le_two_cases {ι : Type*}
    [Fintype ι] [DecidableEq ι] (α : ι → ℕ) (h : (∑ i, α i) ≤ 2) :
    α = 0 ∨ (∃ i, α = Pi.single i 1) ∨
      (∃ i j, α = Pi.single i 1 + Pi.single j 1) := by
  have hs : (∑ i, α i) = 0 ∨ (∑ i, α i) = 1 ∨ (∑ i, α i) = 2 := by omega
  rcases hs with hs | hs | hs
  · exact Or.inl (finite_multiindex_eq_zero_of_sum_eq_zero α hs)
  · exact Or.inr (Or.inl (finite_multiindex_single_of_sum_eq_one α hs))
  · exact Or.inr (Or.inr (finite_multiindex_two_singles_of_sum_eq_two α hs))

theorem factorial_outer_derivative_six_cases
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (h : (∑ i, α i) + (∑ j, β j) ≤ 2) :
    (α = 0 ∧ β = 0) ∨
    (∃ i, α = Pi.single i 1 ∧ β = 0) ∨
    (∃ j, α = 0 ∧ β = Pi.single j 1) ∨
    (∃ i j, α = Pi.single i 1 + Pi.single j 1 ∧ β = 0) ∨
    (∃ i j, α = Pi.single i 1 ∧ β = Pi.single j 1) ∨
    (∃ i j, α = 0 ∧ β = Pi.single i 1 + Pi.single j 1) := by
  have hs : ((∑ i, α i) = 0 ∧ (∑ j, β j) = 0) ∨
      ((∑ i, α i) = 1 ∧ (∑ j, β j) = 0) ∨
      ((∑ i, α i) = 0 ∧ (∑ j, β j) = 1) ∨
      ((∑ i, α i) = 2 ∧ (∑ j, β j) = 0) ∨
      ((∑ i, α i) = 1 ∧ (∑ j, β j) = 1) ∨
      ((∑ i, α i) = 0 ∧ (∑ j, β j) = 2) := by omega
  rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨finite_multiindex_eq_zero_of_sum_eq_zero α ha,
      finite_multiindex_eq_zero_of_sum_eq_zero β hb⟩
  · obtain ⟨i, hi⟩ := finite_multiindex_single_of_sum_eq_one α ha
    exact Or.inr (Or.inl ⟨i, hi, finite_multiindex_eq_zero_of_sum_eq_zero β hb⟩)
  · obtain ⟨j, hj⟩ := finite_multiindex_single_of_sum_eq_one β hb
    exact Or.inr (Or.inr (Or.inl ⟨j, finite_multiindex_eq_zero_of_sum_eq_zero α ha, hj⟩))
  · obtain ⟨i, j, hij⟩ := finite_multiindex_two_singles_of_sum_eq_two α ha
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨i, j, hij, finite_multiindex_eq_zero_of_sum_eq_zero β hb⟩)))
  · obtain ⟨i, hi⟩ := finite_multiindex_single_of_sum_eq_one α ha
    obtain ⟨j, hj⟩ := finite_multiindex_single_of_sum_eq_one β hb
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, hi, hj⟩))))
  · obtain ⟨i, j, hij⟩ := finite_multiindex_two_singles_of_sum_eq_two β hb
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨i, j, finite_multiindex_eq_zero_of_sum_eq_zero α ha, hij⟩))))

end TheoremT.Continuum.WeakGrushin
