import GrushinFactorialOuterIndex_v1
import GrushinFactorialRawCommutatorL2_v1

/-! Actual monomial-weighted L2 representatives for the exact R3 set.
The derivative family remains an explicit input; this module does not
assert that an arbitrary indexed family consists of genuine derivatives. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

def factorialYMonomial (γ : Fin 4 → ℕ) (y : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  ∏ i, (y i)^(γ i)

theorem factorialYMonomial_square (i : Fin 4) (y : EuclideanSpace ℝ (Fin 4)) :
    factorialYMonomial (Pi.single i 2) y = (y i)^2 := by
  classical
  unfold factorialYMonomial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_apply,hji]
  · simp

theorem factorialYMonomial_zero (y : EuclideanSpace ℝ (Fin 4)) :
    factorialYMonomial 0 y = 1 := by
  simp [factorialYMonomial]

def FactorialOuterL2Rep {μ : Measure (Space (Fin 3))}
    (D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (W : FactorialOuterIndex → Lp ℂ 2 μ) : Prop :=
  ∀ m ∈ factorialOuterIndices,
    W m =ᵐ[μ] (fun p => factorialYMonomial m.2.2 p.1 • D m.1 m.2.1 p)

theorem factorial_outer_square_row_L2 {μ : Measure (Space (Fin 3))}
    (D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (W : FactorialOuterIndex → Lp ℂ 2 μ) (hW : FactorialOuterL2Rep D W)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (h : (∑ i, α i)+(∑ j, β j) ≤ 2) :
    ∃ w : Fin 4 → Lp ℂ 2 μ,
      (∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • D α β p)) ∧
      (∑ l, ‖w l‖) ≤ factorialOuterNorm W := by
  refine ⟨(fun l => W (factorialSquareOuterIndex α β l)),?_,
    factorialSquareOuterIndex_norm_sum_le W α β h⟩
  intro l
  have hw := hW (factorialSquareOuterIndex α β l) (factorialSquareOuterIndex_mem α β h l)
  simpa only [factorialSquareOuterIndex,factorialYMonomial_square] using hw

end TheoremT.Continuum.WeakGrushin
