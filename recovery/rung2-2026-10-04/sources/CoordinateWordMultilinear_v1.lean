import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! A literal product of coordinate projections, as a continuous multilinear
map. Its operator norm is at most one for the ordinary finite Pi norm. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} [Fintype σ] {n : ℕ}

def coordinateWordMultilinear (w : Fin n → σ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => σ → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
    (fun j => ContinuousLinearMap.proj (w j))

theorem coordinateWordMultilinear_apply (w : Fin n → σ) (x : Fin n → σ → ℂ) :
    coordinateWordMultilinear w x = ∏ j : Fin n, x j (w j) := by
  simp [coordinateWordMultilinear,ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn]

theorem coordinateWordMultilinear_norm_le (w : Fin n → σ) :
    ‖coordinateWordMultilinear w‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [coordinateWordMultilinear_apply,norm_prod,one_mul]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  exact norm_le_pi_norm (x j) (w j)

theorem coordinateWordMultilinear_diagonal (w : Fin n → σ) (z : σ → ℂ) :
    coordinateWordMultilinear w (fun _ => z) = ∏ j : Fin n, z (w j) :=
  coordinateWordMultilinear_apply w (fun _ => z)

end TheoremT.Continuum
