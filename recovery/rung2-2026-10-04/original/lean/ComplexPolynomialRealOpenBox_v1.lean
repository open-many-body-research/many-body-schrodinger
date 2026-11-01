import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-! A complex polynomial is determined by its values on any positive-radius
real coordinate box. Each side is the complex image of the infinite real
interval (-r,r). Polynomial extensionality on that product proves equality;
no complex openness of the real box is assumed. The variable index type is
arbitrary because every multivariate polynomial has finite variable support. -/
set_option autoImplicit false
namespace TheoremT.Continuum

theorem complexPolynomial_eq_of_real_openBox_eval_eq {σ : Type*}
    (P Q : MvPolynomial σ ℂ) {r : ℝ} (hr : 0 < r)
    (h : ∀ x : σ → ℝ, (∀ i, |x i| < r) →
      MvPolynomial.eval (fun i => (x i : ℂ)) P =
        MvPolynomial.eval (fun i => (x i : ℂ)) Q) : P=Q := by
  classical
  have hinterval : (Set.Ioo (-r) r).Infinite := Set.Ioo_infinite (by linarith)
  apply MvPolynomial.funext_set (fun _ : σ => Complex.ofReal '' Set.Ioo (-r) r)
    (fun _ => hinterval.image Complex.ofReal_injective.injOn)
  intro x hx
  have hx' : ∀ i : σ, ∃ t : ℝ, (-r < t ∧ t < r) ∧ (t : ℂ)=x i := by
    intro i
    rcases hx i (Set.mem_univ i) with ⟨t, ht, heq⟩
    exact ⟨t, ht, heq⟩
  choose y hy hcast using hx'
  have hyabs : ∀ i, |y i| < r := fun i => abs_lt.mpr (hy i)
  simpa only [hcast] using h y hyabs

end TheoremT.Continuum
