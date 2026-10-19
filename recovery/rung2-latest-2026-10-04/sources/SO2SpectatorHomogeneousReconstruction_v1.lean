import SO2SpectatorCoefficientPolynomial_v1
import GroupedHomogeneousSpectatorPolynomial_v1
import Mathlib.Algebra.MvPolynomial.Funext

/-! Adapted from immutable KSSpectatorHomogeneousReconstruction_v1.
Exact finite reconstruction by spectator exponents of a homogeneous joint
polynomial. The finite exponent set depends only on the total degree. Grouping
the literal extracted coefficient family recovers the original polynomial;
no convergence or infinite regrouping is asserted here. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def so2SpectatorTailIndex (w : Fin 3 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i.succ)

def so2SpectatorDegreeIndices (n : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (spectatorTotalDegreeIndices 2 n).image so2SpectatorTailIndex

theorem so2SpectatorTailIndex_degree (w : Fin 3 →₀ ℕ) :
    (so2SpectatorTailIndex w).degree = ∑ i : Fin 2, w i.succ := by
  simp [so2SpectatorTailIndex,Finsupp.degree_eq_sum]

theorem so2SpectatorTailIndex_injective_on_degree (n : ℕ)
    {w v : Fin 3 →₀ ℕ} (hw : w ∈ spectatorTotalDegreeIndices 2 n)
    (hv : v ∈ spectatorTotalDegreeIndices 2 n)
    (h : so2SpectatorTailIndex w = so2SpectatorTailIndex v) : w=v := by
  have ht (i : Fin 2) : w i.succ=v i.succ := congrArg (fun γ : Fin 2 →₀ ℕ => γ i) h
  have hw' := (mem_spectatorTotalDegreeIndices_iff 2 n w).mp hw
  have hv' := (mem_spectatorTotalDegreeIndices_iff 2 n v).mp hv
  have hs : (∑ i : Fin 2, w i.succ) = ∑ i : Fin 2, v i.succ := Finset.sum_congr rfl (fun i _ => ht i)
  ext i
  refine Fin.cases ?_ (fun j => ht j) i
  omega

theorem mem_so2SpectatorDegreeIndices_iff (n : ℕ) (γ : Fin 2 →₀ ℕ) :
    γ ∈ so2SpectatorDegreeIndices n ↔ γ.degree≤n := by
  classical
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp h
    rw [so2SpectatorTailIndex_degree]
    have hh := (mem_spectatorTotalDegreeIndices_iff 2 n w).mp hw
    omega
  · intro h
    let w : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (Fin.cons (n-γ.degree) γ)
    apply Finset.mem_image.mpr
    refine ⟨w,?_,?_⟩
    · apply (mem_spectatorTotalDegreeIndices_iff 2 n w).mpr
      change (n-γ.degree) + (∑ i : Fin 2, γ i)=n
      rw [← Finsupp.degree_eq_sum]
      omega
    · ext i
      rfl

theorem so2SpectatorCoefficientPolynomial_eval_reconstruct_degree
    {P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ} {n : ℕ} (hP : P.IsHomogeneous n)
    (y : Fin 2 → ℂ) (t : Fin 2 → ℂ) :
    eval (Sum.elim y t) P =
      ∑ γ ∈ so2SpectatorDegreeIndices n,
        eval y (so2SpectatorCoefficientPolynomial P γ) * ∏ i : Fin 2, t i ^ γ i := by
  classical
  rw [so2SpectatorCoefficientPolynomial_eval_reconstruct]
  apply Finset.sum_subset
  · intro γ hγ
    apply (mem_so2SpectatorDegreeIndices_iff n γ).mpr
    by_contra hn
    have hz := so2SpectatorCoefficientPolynomial_eq_zero_of_degree_lt hP γ (by omega)
    exact (mem_support_iff.mp hγ) hz
  · intro γ _ hγ
    have hz : so2SpectatorCoefficientPolynomial P γ=0 := by
      exact Classical.byContradiction (fun hz => hγ (mem_support_iff.mpr hz))
    simp [hz]

theorem so2SpectatorCoefficientPolynomial_grouped_reconstruct
    (P : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hP : ∀ n, (P n).IsHomogeneous n) (n : ℕ) :
    groupedHomogeneousSpectatorPolynomial
      (fun j γ => so2SpectatorCoefficientPolynomial (P (j+∑ i : Fin 2, γ i))
        (Finsupp.equivFunOnFinite.symm γ)) n = P n := by
  classical
  apply MvPolynomial.funext
  intro z
  let y : Fin 2 → ℂ := fun i => z (Sum.inl i)
  let t : Fin 2 → ℂ := fun i => z (Sum.inr i)
  have hz : z=Sum.elim y t := by funext i; cases i <;> rfl
  rw [hz,so2SpectatorCoefficientPolynomial_eval_reconstruct_degree (hP n)]
  unfold groupedHomogeneousSpectatorPolynomial
  rw [map_sum]
  simp only [homogeneousSpectatorPolynomial_eval]
  calc
    _ = ∑ w ∈ spectatorTotalDegreeIndices 2 n,
        eval y (so2SpectatorCoefficientPolynomial (P n) (so2SpectatorTailIndex w)) *
          ∏ i : Fin 2, t i ^ (so2SpectatorTailIndex w) i := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [(mem_spectatorTotalDegreeIndices_iff 2 n w).mp hw]
      rfl
    _ = _ := by
      unfold so2SpectatorDegreeIndices
      rw [Finset.sum_image]
      intro w hw v hv h
      exact so2SpectatorTailIndex_injective_on_degree n hw hv h

end TheoremT.Continuum
