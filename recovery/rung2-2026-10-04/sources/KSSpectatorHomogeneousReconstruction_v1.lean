import KSSpectatorCoefficientPolynomial_v1
import GroupedHomogeneousSpectatorPolynomial_v1
import Mathlib.Algebra.MvPolynomial.Funext

/-! Exact finite reconstruction by spectator exponents of a homogeneous joint
polynomial. The finite exponent set depends only on the total degree. Grouping
the literal extracted coefficient family recovers the original polynomial;
no convergence or infinite regrouping is asserted here. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def ksSpectatorTailIndex (w : Fin 4 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i.succ)

def ksSpectatorDegreeIndices (n : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (spectatorTotalDegreeIndices 3 n).image ksSpectatorTailIndex

theorem ksSpectatorTailIndex_degree (w : Fin 4 →₀ ℕ) :
    (ksSpectatorTailIndex w).degree = ∑ i : Fin 3, w i.succ := by
  simp [ksSpectatorTailIndex,Finsupp.degree_eq_sum]

theorem ksSpectatorTailIndex_injective_on_degree (n : ℕ)
    {w v : Fin 4 →₀ ℕ} (hw : w ∈ spectatorTotalDegreeIndices 3 n)
    (hv : v ∈ spectatorTotalDegreeIndices 3 n)
    (h : ksSpectatorTailIndex w = ksSpectatorTailIndex v) : w=v := by
  have ht (i : Fin 3) : w i.succ=v i.succ := congrArg (fun γ : Fin 3 →₀ ℕ => γ i) h
  have hw' := (mem_spectatorTotalDegreeIndices_iff 3 n w).mp hw
  have hv' := (mem_spectatorTotalDegreeIndices_iff 3 n v).mp hv
  have hs : (∑ i : Fin 3, w i.succ) = ∑ i : Fin 3, v i.succ := Finset.sum_congr rfl (fun i _ => ht i)
  ext i
  refine Fin.cases ?_ (fun j => ht j) i
  omega

theorem mem_ksSpectatorDegreeIndices_iff (n : ℕ) (γ : Fin 3 →₀ ℕ) :
    γ ∈ ksSpectatorDegreeIndices n ↔ γ.degree≤n := by
  classical
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp h
    rw [ksSpectatorTailIndex_degree]
    have hh := (mem_spectatorTotalDegreeIndices_iff 3 n w).mp hw
    omega
  · intro h
    let w : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm (Fin.cons (n-γ.degree) γ)
    apply Finset.mem_image.mpr
    refine ⟨w,?_,?_⟩
    · apply (mem_spectatorTotalDegreeIndices_iff 3 n w).mpr
      change (n-γ.degree) + (∑ i : Fin 3, γ i)=n
      rw [← Finsupp.degree_eq_sum]
      omega
    · ext i
      rfl

theorem ksSpectatorCoefficientPolynomial_eval_reconstruct_degree
    {P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ} {n : ℕ} (hP : P.IsHomogeneous n)
    (y : Fin 4 → ℂ) (t : Fin 3 → ℂ) :
    eval (Sum.elim y t) P =
      ∑ γ ∈ ksSpectatorDegreeIndices n,
        eval y (ksSpectatorCoefficientPolynomial P γ) * ∏ i : Fin 3, t i ^ γ i := by
  classical
  rw [ksSpectatorCoefficientPolynomial_eval_reconstruct]
  apply Finset.sum_subset
  · intro γ hγ
    apply (mem_ksSpectatorDegreeIndices_iff n γ).mpr
    by_contra hn
    have hz := ksSpectatorCoefficientPolynomial_eq_zero_of_degree_lt hP γ (by omega)
    exact (mem_support_iff.mp hγ) hz
  · intro γ _ hγ
    have hz : ksSpectatorCoefficientPolynomial P γ=0 := by
      exact Classical.byContradiction (fun hz => hγ (mem_support_iff.mpr hz))
    simp [hz]

theorem ksSpectatorCoefficientPolynomial_grouped_reconstruct
    (P : ℕ → MvPolynomial (Fin 4 ⊕ Fin 3) ℂ)
    (hP : ∀ n, (P n).IsHomogeneous n) (n : ℕ) :
    groupedHomogeneousSpectatorPolynomial
      (fun j γ => ksSpectatorCoefficientPolynomial (P (j+∑ i : Fin 3, γ i))
        (Finsupp.equivFunOnFinite.symm γ)) n = P n := by
  classical
  apply MvPolynomial.funext
  intro z
  let y : Fin 4 → ℂ := fun i => z (Sum.inl i)
  let t : Fin 3 → ℂ := fun i => z (Sum.inr i)
  have hz : z=Sum.elim y t := by funext i; cases i <;> rfl
  rw [hz,ksSpectatorCoefficientPolynomial_eval_reconstruct_degree (hP n)]
  unfold groupedHomogeneousSpectatorPolynomial
  rw [map_sum]
  simp only [homogeneousSpectatorPolynomial_eval]
  calc
    _ = ∑ w ∈ spectatorTotalDegreeIndices 3 n,
        eval y (ksSpectatorCoefficientPolynomial (P n) (ksSpectatorTailIndex w)) *
          ∏ i : Fin 3, t i ^ (ksSpectatorTailIndex w) i := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [(mem_spectatorTotalDegreeIndices_iff 3 n w).mp hw]
      rfl
    _ = _ := by
      unfold ksSpectatorDegreeIndices
      rw [Finset.sum_image]
      intro w hw v hv h
      exact ksSpectatorTailIndex_injective_on_degree n hw hv h

end TheoremT.Continuum
