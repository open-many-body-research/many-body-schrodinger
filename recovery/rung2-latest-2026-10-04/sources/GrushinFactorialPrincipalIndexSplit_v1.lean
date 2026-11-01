import GrushinFactorialIndexDecomposition_v1

/-! Actual componentwise R14 decompositions. These establish both the
correct target multiindices and membership in the exact weighted set M,
not only total-degree inequalities. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_multiindex_sum_sub {ι : Type*} [Fintype ι]
    (α η : ι → ℕ) (h : ∀ i, η i ≤ α i) :
    (∑ i, (α i-η i)) = (∑ i, α i)-(∑ i, η i) := by
  have hs : (∑ i, (α i-η i))+(∑ i, η i) = ∑ i, α i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (h i))
  omega

theorem factorial_multiindex_single_le {ι : Type*} [DecidableEq ι]
    (α : ι → ℕ) (i : ι) (n : ℕ) (h : n ≤ α i) :
    ∀ l, (Pi.single i n : ι → ℕ) l ≤ α l := by
  intro l
  by_cases hl : l = i
  · subst l; simpa using h
  · simp [hl]

theorem factorial_multiindex_double_single {ι : Type*} [DecidableEq ι]
    (β : ι → ℕ) (j : ι) : (β+Pi.single j 1)+Pi.single j 1 = β+Pi.single j 2 := by
  funext l
  by_cases hl : l = j
  · subst l; simp
  · simp [Pi.add_apply,hl]

theorem factorial_principal_one_hit_split
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (i : Fin 4) (j : Fin 3)
    (hi : 1 ≤ α i) :
    ∃ a η : Fin 4 → ℕ,
      a+η = (fun l => α l-(Pi.single i 1 : Fin 4 → ℕ) l) ∧
      (η,Pi.single j 1,Pi.single i 1) ∈ factorialOuterIndices ∧
      factorialMultiDerivativeCost a (β+Pi.single j 1)+1 ≤ factorialMultiDerivativeCost α β := by
  let A := ∑ l, α l
  let B := ∑ l, β l
  let q : Fin 4 → ℕ := fun l => α l-(Pi.single i 1 : Fin 4 → ℕ) l
  have hAi : 1 ≤ A := hi.trans (Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ i))
  have hq : (∑ l, q l) = A-1 := by
    simpa [q,A] using factorial_multiindex_sum_sub α (Pi.single i 1)
      (factorial_multiindex_single_le α i 1 hi)
  have hb : (∑ l, (β+Pi.single j 1 : Fin 3 → ℕ) l) = B+1 := by
    simp [B,Pi.add_apply,Finset.sum_add_distrib]
  by_cases hA : A = 1
  · refine ⟨q,0,by simp [q],?_,?_⟩
    · rw [factorialOuterIndices_mem]
      simp [factorialOuterAdmissible]
    · unfold factorialMultiDerivativeCost
      change _ ≤ factorialDerivativeCost A B
      rw [hq,hb,hA]
      exact (factorialDerivativeCost_one_hit_low B).le
  · obtain ⟨η,hη,hηn⟩ := finite_submultiindex_degree q 1 (by omega)
    let a : Fin 4 → ℕ := fun l => q l-η l
    have ha : a+η=q := by funext l; exact Nat.sub_add_cancel (hη l)
    have han : (∑ l, a l) = A-2 := by
      have := factorial_multiindex_sum_sub q η hη
      dsimp [a]
      rw [this,hq,hηn]
      omega
    refine ⟨a,η,ha,?_,?_⟩
    · rw [factorialOuterIndices_mem]
      simp [factorialOuterAdmissible,hηn]
    · unfold factorialMultiDerivativeCost
      change _ ≤ factorialDerivativeCost A B
      rw [han,hb]
      exact factorialDerivativeCost_one_hit_high (by omega)

theorem factorial_principal_two_hit_split
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (i : Fin 4) (j : Fin 3)
    (hi : 2 ≤ α i) :
    ∃ a : Fin 4 → ℕ, ∃ b : Fin 3 → ℕ,
    ∃ η : Fin 4 → ℕ, ∃ θ : Fin 3 → ℕ,
      a+η = (fun l => α l-(Pi.single i 2 : Fin 4 → ℕ) l) ∧
      b+θ = β+Pi.single j 2 ∧
      (η,θ,0) ∈ factorialOuterIndices ∧
      factorialMultiDerivativeCost a b+2 ≤ factorialMultiDerivativeCost α β := by
  let A := ∑ l, α l
  let B := ∑ l, β l
  let q : Fin 4 → ℕ := fun l => α l-(Pi.single i 2 : Fin 4 → ℕ) l
  have hAi : 2 ≤ A := hi.trans (Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ i))
  have hq : (∑ l, q l) = A-2 := by
    simpa [q,A] using factorial_multiindex_sum_sub α (Pi.single i 2)
      (factorial_multiindex_single_le α i 2 hi)
  by_cases hA : A ≤ 3
  · refine ⟨q,β+Pi.single j 1,0,Pi.single j 1,by simp [q],
      factorial_multiindex_double_single β j,?_,?_⟩
    · rw [factorialOuterIndices_mem]
      simp [factorialOuterAdmissible]
    · have hb : (∑ l, (β+Pi.single j 1 : Fin 3 → ℕ) l) = B+1 := by
        simp [B,Pi.add_apply,Finset.sum_add_distrib]
      unfold factorialMultiDerivativeCost
      change _ ≤ factorialDerivativeCost A B
      rw [hq,hb]
      have := factorialDerivativeCost_two_hit_low (B := B) hAi hA
      omega
  · obtain ⟨η,hη,hηn⟩ := finite_submultiindex_degree q 2 (by omega)
    let a : Fin 4 → ℕ := fun l => q l-η l
    have ha : a+η=q := by funext l; exact Nat.sub_add_cancel (hη l)
    have han : (∑ l, a l) = A-4 := by
      have := factorial_multiindex_sum_sub q η hη
      dsimp [a]
      rw [this,hq,hηn]
      omega
    refine ⟨a,β+Pi.single j 2,η,0,ha,by simp,?_,?_⟩
    · rw [factorialOuterIndices_mem]
      simp [factorialOuterAdmissible,hηn]
    · have hb : (∑ l, (β+Pi.single j 2 : Fin 3 → ℕ) l) = B+2 := by
        simp [B,Pi.add_apply,Finset.sum_add_distrib]
      unfold factorialMultiDerivativeCost
      change _ ≤ factorialDerivativeCost A B
      rw [han,hb]
      exact factorialDerivativeCost_two_hit_high (by omega)

end TheoremT.Continuum.WeakGrushin
