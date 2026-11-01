import HomogeneousSpectatorPolynomial_v1
import SpectatorTotalDegreeIndices_v1

/-! Literal finite grouping by joint total degree. Each block sums exactly
the actual pairs (m,gamma) with m + sum(gamma) = n. The resulting coefficient
bound retains the binomial multiplicity instead of replacing it by an
exponential factor. Infinite-series reindexing is a separate next step. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} {d : ℕ}

def groupedHomogeneousSpectatorPolynomial
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ) (n : ℕ) :
    MvPolynomial (σ ⊕ Fin d) ℂ :=
  ∑ w ∈ spectatorTotalDegreeIndices d n,
    homogeneousSpectatorPolynomial (A (w 0) (fun i => w i.succ)) (fun i => w i.succ)

theorem groupedHomogeneousSpectatorPolynomial_isHomogeneous
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) (n : ℕ) :
    (groupedHomogeneousSpectatorPolynomial A n).IsHomogeneous n := by
  apply MvPolynomial.IsHomogeneous.sum
  intro w hw
  have hn := (mem_spectatorTotalDegreeIndices_iff d n w).mp hw
  simpa only [hn] using homogeneousSpectatorPolynomial_isHomogeneous
    (hA (w 0) (fun i => w i.succ)) (fun i => w i.succ)

theorem polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ) {M T : ℝ}
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin d, γ i))
    (n : ℕ) :
    polynomialCoeffL1 (groupedHomogeneousSpectatorPolynomial A n) ≤
      M*((n+d).choose d : ℝ)*T^n := by
  apply (polynomialCoeffL1_sum _ _).trans
  calc
    _ ≤ ∑ _w ∈ spectatorTotalDegreeIndices d n, M*T^n := by
      apply Finset.sum_le_sum
      intro w hw
      have hn := (mem_spectatorTotalDegreeIndices_iff d n w).mp hw
      exact (polynomialCoeffL1_homogeneousSpectatorPolynomial _ _).trans
        (by simpa only [hn] using hL (w 0) (fun i => w i.succ))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul,card_spectatorTotalDegreeIndices]; ring

end TheoremT.Continuum
