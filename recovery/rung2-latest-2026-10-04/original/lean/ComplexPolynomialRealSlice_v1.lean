import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A complex polynomial is determined by its values on the entire real slice.
This uses genuine polynomial extensionality on the product of the infinite
real-coordinate subsets of complex numbers. It does not assume that a real
slice is a complex open set, or that arbitrary functions admit this extension. -/
set_option autoImplicit false
namespace TheoremT.Continuum

theorem complexPolynomial_eq_of_real_eval_eq {σ : Type*}
    (P Q : MvPolynomial σ ℂ)
    (h : ∀ x : σ → ℝ,
      MvPolynomial.eval (fun i => (x i : ℂ)) P =
        MvPolynomial.eval (fun i => (x i : ℂ)) Q) : P=Q := by
  classical
  apply MvPolynomial.funext_set (fun _ : σ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  have hx' : ∀ i : σ, ∃ r : ℝ, (r : ℂ)=x i :=
    fun i => hx i (Set.mem_univ i)
  choose y hy using hx'
  simpa only [hy] using h y

end TheoremT.Continuum
