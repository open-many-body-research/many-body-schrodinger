import HomogeneousPolynomialEvaluationBound_v1
import HomogeneousPolynomialMultilinear_v1

/-! Independent boundary checks: zero arity, empty coordinate type, and the
zero polynomial in arbitrary degree. These specialize the reviewed APIs. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

example (c : ℂ) :
    ‖MvPolynomial.eval (fun i : Fin 0 => Fin.elim0 i)
      (MvPolynomial.C c : MvPolynomial (Fin 0) ℂ)‖ ≤ ‖c‖ := by
  have h := homogeneous_polynomial_eval_norm_bound
    (MvPolynomial.C c : MvPolynomial (Fin 0) ℂ) (MvPolynomial.isHomogeneous_C _ c)
    (fun i : Fin 0 => Fin.elim0 i) (r := 0) le_rfl (fun i => Fin.elim0 i)
  simpa [polynomialCoeffL1_C] using h

example (c : ℂ) :
    ∃ L : ContinuousMultilinearMap ℂ (fun _ : Fin 0 => Fin 0 → ℂ) ℂ,
      (∀ z : Fin 0 → ℂ, L (fun _ => z) = c) ∧ ‖L‖ ≤ ‖c‖ := by
  simpa only [MvPolynomial.eval_C, polynomialCoeffL1_C] using
    homogeneous_polynomial_multilinear_exists
      (MvPolynomial.C c : MvPolynomial (Fin 0) ℂ) (MvPolynomial.isHomogeneous_C _ c)

example : ∃ w : Fin 0 → Fin 0, ∀ z : Fin 0 → ℂ,
    (∏ j : Fin 0, z (w j)) = 1 := by
  obtain ⟨w, hw⟩ := monomial_exponent_word_exists (M := ℂ) (0 : Fin 0 →₀ ℕ) 0 (by simp)
  refine ⟨w, ?_⟩
  intro z
  simpa using hw z

example {σ : Type*} [Fintype σ] (n : ℕ) :
    ∃ L : ContinuousMultilinearMap ℂ (fun _ : Fin n => σ → ℂ) ℂ,
      (∀ z : σ → ℂ, L (fun _ => z) = 0) ∧ ‖L‖ ≤ 0 := by
  simpa only [map_zero, polynomialCoeffL1_zero] using
    homogeneous_polynomial_multilinear_exists (0 : MvPolynomial σ ℂ)
      (MvPolynomial.isHomogeneous_zero σ ℂ n)

end TheoremT.Continuum
