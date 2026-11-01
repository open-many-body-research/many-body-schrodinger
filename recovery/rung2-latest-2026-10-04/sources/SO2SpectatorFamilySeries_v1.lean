import SO2SpectatorHomogeneousReconstruction_v1
import HomogeneousSpectatorFiniteVariables_v1
import SpectatorPolynomialSeriesReindex_v1

/-! Actual double-family extraction and reconstruction of a joint
two-plus-two homogeneous polynomial series. Absolute summability follows
from the given coefficient budget. Equality to the original joint sum
is proved by finite reconstruction and the existing justified grouping. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def so2SpectatorFamily (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (j : ℕ) (γ : Fin 2 → ℕ) : MvPolynomial (Fin 2) ℂ :=
  so2SpectatorCoefficientPolynomial (Q (j+∑ i : Fin 2, γ i))
    (Finsupp.equivFunOnFinite.symm γ)

theorem so2SpectatorFamily_homogeneous
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) (j : ℕ) (γ : Fin 2 → ℕ) :
    (so2SpectatorFamily Q j γ).IsHomogeneous j := by
  have hg : (Finsupp.equivFunOnFinite.symm γ).degree = ∑ i : Fin 2, γ i := by
    simp [Finsupp.degree_eq_sum]
  simpa only [so2SpectatorFamily,hg,Nat.add_sub_cancel] using
    so2SpectatorCoefficientPolynomial_homogeneous (hQ (j+∑ i : Fin 2, γ i))
      (Finsupp.equivFunOnFinite.symm γ)

theorem so2SpectatorFamily_coefficientL1
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) {C B : ℝ}
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n) (j : ℕ) (γ : Fin 2 → ℕ) :
    polynomialCoeffL1 (so2SpectatorFamily Q j γ) ≤ C*B^j*B^(∑ i : Fin 2, γ i) := by
  have hh := (polynomialCoeffL1_so2SpectatorCoefficientPolynomial
    (Q (j+∑ i : Fin 2, γ i)) (Finsupp.equivFunOnFinite.symm γ)).trans
      (hL (j+∑ i : Fin 2, γ i))
  simpa only [so2SpectatorFamily,pow_add,mul_assoc] using hh

theorem so2SpectatorFamily_grouped
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) (n : ℕ) :
    groupedHomogeneousSpectatorPolynomial (so2SpectatorFamily Q) n = Q n :=
  so2SpectatorCoefficientPolynomial_grouped_reconstruct Q hQ n

theorem so2SpectatorFamily_summable
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) {C B : ℝ} (hC : 0≤C) (hB : 0≤B)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (y t : Fin 2 → ℂ) (hy : B*‖y‖<1) (ht : B*‖t‖<1) :
    Summable (fun k : ℕ × (Fin 2 → ℕ) =>
      ‖eval y (so2SpectatorFamily Q k.1 k.2)*∏ i : Fin 2, t i^k.2 i‖) ∧
    Summable (fun k : ℕ × (Fin 2 → ℕ) =>
      eval y (so2SpectatorFamily Q k.1 k.2)*∏ i : Fin 2, t i^k.2 i) :=
  homogeneous_spectator_finite_variables_summable _ (so2SpectatorFamily_homogeneous Q hQ)
    hC hB (norm_nonneg y) hB (norm_nonneg t) hy ht
    (so2SpectatorFamily_coefficientL1 Q hL) y t
    (fun i => norm_le_pi_norm y i) (fun i => norm_le_pi_norm t i)

theorem so2SpectatorFamily_hasSum_of_joint_hasSum
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) {C B : ℝ} (hC : 0≤C) (hB : 0≤B)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (y t : Fin 2 → ℂ) (hy : B*‖y‖<1) (ht : B*‖t‖<1) {v : ℂ}
    (hsum : HasSum (fun n => eval (Sum.elim y t) (Q n)) v) :
    HasSum (fun k : ℕ × (Fin 2 → ℕ) =>
      eval y (so2SpectatorFamily Q k.1 k.2)*∏ i : Fin 2, t i^k.2 i) v := by
  have hs := (so2SpectatorFamily_summable Q hQ hC hB hL y t hy ht).2
  have hg := groupedHomogeneousSpectatorPolynomial_hasSum (so2SpectatorFamily Q) y t hs
  simp only [so2SpectatorFamily_grouped Q hQ] at hg
  have hv := hsum.unique hg
  rw [hv]
  exact hs.hasSum

end TheoremT.Continuum
