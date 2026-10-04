import ManyBody.S8.Internal.RealTaylorDistanceDictionary
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fintype.BigOperators
/-! Degree and cardinality of the genuine three-distance Taylor dictionary.

The actual translated multilinear word expansion has total degree below the
cutoff order at each supported exponent. Its literal unshifted support embeds
in the coordinate box {0,...,N-1}^3, giving at most N^3 monomials, including
the empty order-zero dictionary. Coefficients are the actual real polynomial
coefficients, with no assumed finite representation or computable extraction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ManyBody.S8

theorem realTaylorMvPolynomial_totalDegree_le (f : (Fin 3 → ℝ) → ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) :
    (realTaylorMvPolynomial f a N).totalDegree≤N-1 := by
  classical
  unfold realTaylorMvPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  apply MvPolynomial.totalDegree_finsetSum_le
  intro w hw
  calc
    _≤(MvPolynomial.C ((n.factorial:ℝ)⁻¹*
        iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1))).totalDegree+
        (∏ k, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _≤0+∑ k : Fin n, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k))).totalDegree := by
      rw [MvPolynomial.totalDegree_C]
      exact Nat.add_le_add_left (MvPolynomial.totalDegree_finsetProd _ _) 0
    _≤∑ _k : Fin n, 1 := by
      simp only [zero_add]
      apply Finset.sum_le_sum
      intro k hk
      exact (MvPolynomial.totalDegree_sub_C_le _ _).trans_eq (MvPolynomial.totalDegree_X _)
    _=n := by simp
    _≤N-1 := by have := Finset.mem_range.mp hn; omega

theorem realTaylorMvPolynomial_support_total_degree_lt
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ)
    {d : Fin 3 →₀ ℕ} (hd : d∈(realTaylorMvPolynomial f a N).support) :
    ∑ j : Fin 3, d j<N := by
  by_cases hN : N=0
  · simp [hN,realTaylorMvPolynomial] at hd
  have hsum : d.sum (fun _ e => e)=∑ j : Fin 3, d j := d.sum_fintype _ (by simp)
  have hbound := (MvPolynomial.le_totalDegree hd).trans (realTaylorMvPolynomial_totalDegree_le f a N)
  rw [hsum] at hbound
  omega

theorem realTaylorMvPolynomial_support_coordinate_lt
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ)
    {d : Fin 3 →₀ ℕ} (hd : d∈(realTaylorMvPolynomial f a N).support) (j : Fin 3) :
    d j<N :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_lt
    (realTaylorMvPolynomial_support_total_degree_lt f a N hd)

def realTaylorDistanceDictionarySupport (f : (Fin 3 → ℝ) → ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) : Finset DistanceMultiIndex :=
  (realTaylorMvPolynomial f a N).support.image Finsupp.equivFunOnFinite

def realTaylorDistanceDictionaryCoefficient (f : (Fin 3 → ℝ) → ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) (α : DistanceMultiIndex) : ℝ :=
  (realTaylorMvPolynomial f a N).coeff (Finsupp.equivFunOnFinite.symm α)

@[simp] theorem realTaylorDistanceDictionarySupport_zero
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) :
    realTaylorDistanceDictionarySupport f a 0=∅ := by
  simp [realTaylorDistanceDictionarySupport,realTaylorMvPolynomial]

theorem realTaylorPolynomial_exact_distance_dictionary
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ) :
    realTaylorPolynomial f a N=
      realDistancePolynomial (realTaylorDistanceDictionarySupport f a N)
        (realTaylorDistanceDictionaryCoefficient f a N) := by
  classical
  let e : (Fin 3 →₀ ℕ) ≃ DistanceMultiIndex := Finsupp.equivFunOnFinite
  funext p
  rw [←realTaylorMvPolynomial_eval f a N p]
  unfold realTaylorDistanceDictionarySupport realTaylorDistanceDictionaryCoefficient
  rw [MvPolynomial.eval_eq']
  unfold realDistancePolynomial
  rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [smul_eq_mul,realDistanceMonomial]
  change (realTaylorMvPolynomial f a N).coeff d*(∏ j, p j^(d j))=
    (realTaylorMvPolynomial f a N).coeff (e.symm (e d))*(∏ j, p j^((e d) j))
  rw [e.symm_apply_apply]
  rfl

theorem realTaylorDistanceDictionarySupport_card_le
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ) :
    (realTaylorDistanceDictionarySupport f a N).card≤N^3 := by
  classical
  have hsub : realTaylorDistanceDictionarySupport f a N⊆
      Fintype.piFinset (fun _ : Fin 3 => Finset.range N) := by
    intro α hα
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hα
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_range.mpr (realTaylorMvPolynomial_support_coordinate_lt f a N hd j)
  have hcard := Finset.card_le_card hsub
  simpa only [Fintype.card_piFinset_const,Finset.card_range] using hcard

theorem realTaylorMvPolynomial_support_card_le
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ) :
    (realTaylorMvPolynomial f a N).support.card≤N^3 := by
  have h := realTaylorDistanceDictionarySupport_card_le f a N
  rw [realTaylorDistanceDictionarySupport,
    Finset.card_image_of_injective _ Finsupp.equivFunOnFinite.injective] at h
  exact h

theorem realTaylorPolynomial_bounded_finite_dictionary
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N : ℕ) :
    ∃ s : Finset DistanceMultiIndex, ∃ c : DistanceMultiIndex → ℝ,
      s.card≤N^3 ∧ (∀ α∈s, (∑ j : Fin 3, α j)<N) ∧
      realTaylorPolynomial f a N=realDistancePolynomial s c := by
  classical
  let P := realTaylorMvPolynomial f a N
  let e : (Fin 3 →₀ ℕ) ≃ DistanceMultiIndex := Finsupp.equivFunOnFinite
  let s := realTaylorDistanceDictionarySupport f a N
  refine ⟨s,fun α => P.coeff (e.symm α),realTaylorDistanceDictionarySupport_card_le f a N,?_,?_⟩
  · intro α hα
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hα
    exact realTaylorMvPolynomial_support_total_degree_lt f a N hd
  · funext p
    rw [←realTaylorMvPolynomial_eval f a N p]
    dsimp [P,s,realTaylorDistanceDictionarySupport]
    rw [MvPolynomial.eval_eq']
    unfold realDistancePolynomial
    rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [e.symm_apply_apply,smul_eq_mul,realDistanceMonomial]
    rfl

#print axioms realTaylorPolynomial_exact_distance_dictionary
#print axioms realTaylorMvPolynomial_support_total_degree_lt
#print axioms realTaylorMvPolynomial_support_card_le
#print axioms realTaylorPolynomial_bounded_finite_dictionary
end ManyBody.S8
