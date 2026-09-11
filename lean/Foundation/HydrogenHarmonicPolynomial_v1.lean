import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-! Exact symbolic polynomial Laplacian identities for the hydrogen angular
decomposition. These are identities of actual multivariate polynomials.
No identification with weak derivatives or spherical Laplacians is asserted. -/

noncomputable section
open MvPolynomial
open scoped BigOperators

namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ]

def radiusSquared : MvPolynomial σ ℝ := ∑ i : σ, X i ^ 2

def polynomialLaplace (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, pderiv i (pderiv i P)

def polynomialEuler (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, X i * pderiv i P

theorem pderiv_radiusSquared (i : σ) :
    pderiv i (radiusSquared : MvPolynomial σ ℝ) = 2 * X i := by
  classical
  simp [radiusSquared, map_sum, pderiv_X, Pi.single_apply, mul_ite]

theorem pderiv_twice_radiusSquared_mul (i : σ) (P : MvPolynomial σ ℝ) :
    pderiv i (pderiv i (radiusSquared * P)) =
      radiusSquared * pderiv i (pderiv i P) + 4 * (X i * pderiv i P) + 2 * P := by
  have htwo : pderiv i (2 : MvPolynomial σ ℝ) = 0 :=
    (pderiv i).map_natCast 2
  simp only [pderiv_mul, map_add, pderiv_radiusSquared, pderiv_X_self,
    htwo, zero_mul]
  ring

theorem polynomialLaplace_radiusSquared_mul (P : MvPolynomial σ ℝ) :
    polynomialLaplace (radiusSquared * P) =
      radiusSquared * polynomialLaplace P + 4 * polynomialEuler P +
        ((2 * Fintype.card σ : ℕ) : MvPolynomial σ ℝ) * P := by
  simp only [polynomialLaplace, pderiv_twice_radiusSquared_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, polynomialEuler, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem radiusSquared_isHomogeneous :
    (radiusSquared : MvPolynomial σ ℝ).IsHomogeneous 2 := by
  exact IsHomogeneous.sum Finset.univ (fun i : σ => X i ^ 2) 2
    (fun i _ => isHomogeneous_X_pow i 2)

theorem polynomialEuler_of_isHomogeneous {P : MvPolynomial σ ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) : polynomialEuler P = (m : MvPolynomial σ ℝ) * P := by
  simpa only [polynomialEuler, nsmul_eq_mul] using hP.sum_X_mul_pderiv

theorem polynomialLaplace_radiusSquared_mul_three (P : MvPolynomial (Fin 3) ℝ) :
    polynomialLaplace (radiusSquared * P) =
      radiusSquared * polynomialLaplace P + 4 * polynomialEuler P + 6 * P := by
  simpa using polynomialLaplace_radiusSquared_mul P

theorem polynomialLaplace_radius_pow_mul_harmonic_succ
    {H : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) (hLap : polynomialLaplace H = 0) (j : ℕ) :
    polynomialLaplace (radiusSquared ^ (j + 1) * H) =
      ((2 * (j + 1) * (2 * m + 2 * (j + 1) + 1) : ℕ) : MvPolynomial (Fin 3) ℝ) *
        (radiusSquared ^ j * H) := by
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, one_mul]
    rw [polynomialLaplace_radiusSquared_mul_three, hLap, mul_zero, zero_add,
      polynomialEuler_of_isHomogeneous hH]
    push_cast
    ring
  | succ j hj =>
    have hhom : (radiusSquared ^ (j + 1) * H).IsHomogeneous (2 * (j + 1) + m) :=
      (radiusSquared_isHomogeneous.pow (j + 1)).mul hH
    have he : radiusSquared ^ (j + 1 + 1) * H =
        radiusSquared * (radiusSquared ^ (j + 1) * H) := by ring
    change polynomialLaplace (radiusSquared ^ (j + 1 + 1) * H) = _
    rw [he, polynomialLaplace_radiusSquared_mul_three, hj,
      polynomialEuler_of_isHomogeneous hhom]
    push_cast
    rw [pow_succ]
    ring

theorem polynomialLaplace_radius_pow_mul_harmonic
    {H : MvPolynomial (Fin 3) ℝ} {m j : ℕ}
    (hH : H.IsHomogeneous m) (hLap : polynomialLaplace H = 0) (hj : 1 ≤ j) :
    polynomialLaplace (radiusSquared ^ j * H) =
      ((2 * j * (2 * m + 2 * j + 1) : ℕ) : MvPolynomial (Fin 3) ℝ) *
        (radiusSquared ^ (j - 1) * H) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simpa using polynomialLaplace_radius_pow_mul_harmonic_succ hH hLap k

end TheoremT.HydrogenPolynomial
