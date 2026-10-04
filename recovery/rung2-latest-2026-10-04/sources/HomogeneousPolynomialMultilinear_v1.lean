import CoordinateWordMultilinear_v1
import MonomialExponentWord_v1
import MvPolynomialCoefficientL1Substitution_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Every actual homogeneous complex polynomial has a multilinear
representation whose operator norm is at most its literal coefficient L1
norm. The monomial word representatives are selected classically; this is
a mathematical representation theorem, not an executable procedure. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} [Fintype σ]

theorem homogeneous_polynomial_multilinear_exists
    (P : MvPolynomial σ ℂ) {n : ℕ} (hP : P.IsHomogeneous n) :
    ∃ L : ContinuousMultilinearMap ℂ (fun _ : Fin n => σ → ℂ) ℂ,
      (∀ z : σ → ℂ, L (fun _ => z) = MvPolynomial.eval z P) ∧
      ‖L‖ ≤ polynomialCoeffL1 P := by
  classical
  have hword (d : {d // d ∈ P.support}) :
      ∃ w : Fin n → σ, ∀ z : σ → ℂ,
        (∏ j : Fin n, z (w j)) = ∏ i ∈ d.val.support, z i ^ d.val i := by
    exact monomial_exponent_word_exists d.val n (hP.degree_eq_sum_deg_support d.property).symm
  choose w hw using hword
  let L : ContinuousMultilinearMap ℂ (fun _ : Fin n => σ → ℂ) ℂ :=
    ∑ d ∈ P.support.attach, P.coeff d.val • coordinateWordMultilinear (w d)
  refine ⟨L, ?_, ?_⟩
  · intro z
    simp only [L,sum_apply,smul_apply,
      coordinateWordMultilinear_diagonal,smul_eq_mul,hw]
    exact (Finset.sum_attach P.support
      (fun d => P.coeff d * ∏ i ∈ d.support, z i ^ d i)).trans (MvPolynomial.eval_eq z P).symm
  · calc
      ‖L‖ ≤ ∑ d ∈ P.support.attach,
          ‖P.coeff d.val • coordinateWordMultilinear (w d)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ P.support.attach, ‖P.coeff d.val‖ := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_smul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (coordinateWordMultilinear_norm_le (w d)) (norm_nonneg _)
      _ = polynomialCoeffL1 P := by
        exact Finset.sum_attach P.support (fun d => ‖P.coeff d‖)

end TheoremT.Continuum
