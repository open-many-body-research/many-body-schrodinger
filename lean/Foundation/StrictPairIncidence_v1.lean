import WeakCoulombNorm_v2
import PotentialPermutation_v2

/-! Exact incidence counting for the existing strict electron-pair type.
The statement allows arbitrary real weights and includes N = 0. -/

noncomputable section
open scoped BigOperators

namespace TheoremT.Continuum

/-- Real-valued version of the existing strict-pair double-sum identity. -/
theorem strictElectronPair_sum_real {N : ℕ} (a : Fin N → Fin N → ℝ) :
    (∑ q : StrictElectronPair N, a q.val.1 q.val.2) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j), a i j := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2))
    (by simp) (fun q => a q.1 q.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

/-- Each electron is incident to precisely N - 1 strict pairs; the formula
also holds for the empty electron type, where both sums vanish. -/
theorem strictElectronPair_incidence_sum (N : ℕ) (a : Fin N → ℝ) :
    (∑ q : StrictElectronPair N, (a q.val.1 + a q.val.2)) =
      ((N : ℝ) - 1) * ∑ i : Fin N, a i := by
  let b : Fin N → Fin N → ℝ :=
    fun i j => (a i + a j) - if i = j then 2 * a i else 0
  have hsym : ∀ i j, b i j = b j i := by
    intro i j
    by_cases h : i = j
    · subst j
      rfl
    · simp [b, h, Ne.symm h, add_comm]
  have hdiag : ∀ i, b i i = 0 := by
    intro i
    simp [b]
    ring
  have hoff (i j : Fin N) (hij : i < j) : b i j = a i + a j := by
    simp [b, ne_of_lt hij]
  have hs : (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      b i j) = ∑ q : StrictElectronPair N, (a q.val.1 + a q.val.2) := by
    rw [strictElectronPair_sum_real (fun i j => a i + a j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    exact hoff i j (Finset.mem_filter.mp hj).2
  have hfull : (∑ i : Fin N, ∑ j : Fin N, b i j) =
      2 * (((N : ℝ) - 1) * ∑ i : Fin N, a i) := by
    simp only [b, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp [← Finset.mul_sum]
    ring
  have hcount := two_mul_strict_pair_sum b hsym hdiag
  rw [hs, hfull] at hcount
  linarith

#print axioms strictElectronPair_sum_real
#print axioms strictElectronPair_incidence_sum

end TheoremT.Continuum
