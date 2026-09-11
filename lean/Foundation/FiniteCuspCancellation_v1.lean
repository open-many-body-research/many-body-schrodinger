import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Finite algebra only; physical weak jets and the trace identity are supplied
by separate unconditional continuum theorems. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem finite_cusp_cancellation {ι : Type*} [Fintype ι]
    (a t f V E : ℂ) (q l b h d e A B : ι → ℂ)
    (he : (∑ k, e k)=2*(V-E)*f) (hh : (∑ k, h k)=2*V)
    (hA : ∀ k, A k=t*a*d k+t*(q k-a*b k)*f)
    (hB : ∀ k, B k=(t*a*e k+t*(q k-a*b k)*d k)+
      (t*(q k-a*b k)*d k+t*(l k-q k*b k-q k*b k+a*(b k*b k-h k))*f)) :
    (∑ k, B k) = -2*(∑ k, b k*A k)-((∑ k, (b k)^2)+2*E)*(t*a*f)+
      t*((∑ k, l k)*f+2*(∑ k, q k*d k)) := by
  have hp (k : ι) : B k+2*(b k*A k)+(b k)^2*(t*a*f) =
      t*a*e k+t*(l k)*f+2*t*(q k*d k)-t*a*(h k)*f := by
    rw [hA,hB]
    ring
  have hs := congrArg (fun c : ι → ℂ => ∑ k, c k) (funext hp)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    ← Finset.sum_mul] at hs
  rw [he,hh] at hs
  linear_combination hs

#print axioms finite_cusp_cancellation
end TheoremT.Continuum
