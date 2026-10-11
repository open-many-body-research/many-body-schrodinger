import SpectatorIterationBudget_v1
import Mathlib.Order.Monotone.Basic

/-! An explicit norm-budget recurrence for stage-dependent cutoff constants.
The recursion uses exactly the displayed one-step budget at each stage.
Its positivity and monotonicity do not assert that any derivative family
exists, nor do they give an executable approximation or a complexity bound. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

def spectatorIterationBudgetSeq (c : ℝ) (M A B D Q : ℕ → ℝ)
    (Kcoef Hsource Winit : ℝ) : ℕ → ℝ
  | 0 => Winit
  | k+1 => spectatorIterationNext c (M k) (A k) (B k) (D k) (Q k) Kcoef Hsource k
      (spectatorIterationBudgetSeq c M A B D Q Kcoef Hsource Winit k)

theorem spectatorIterationBudgetSeq_nonneg
    (c : ℝ) (M A B D Q : ℕ → ℝ) (Kcoef Hsource Winit : ℝ)
    (hc : 0 < c) (hB : ∀ k, 0 ≤ B k) (hD : ∀ k, 0 ≤ D k) (hQ : ∀ k, 0 ≤ Q k)
    (hKcoef : 0 ≤ Kcoef) (hHsource : 0 ≤ Hsource) (hWinit : 0 ≤ Winit) :
    ∀ k, 0 ≤ spectatorIterationBudgetSeq c M A B D Q Kcoef Hsource Winit k := by
  intro k
  induction k with
  | zero => exact hWinit
  | succ k ih =>
    exact (spectatorIterationBudget_bounds c (M k) (A k) (B k) (D k) (Q k)
      Kcoef Hsource k (spectatorIterationBudgetSeq c M A B D Q Kcoef Hsource Winit k)
      hc (hB k) (hD k) (hQ k) hKcoef hHsource ih).2.1

theorem spectatorIterationBudgetSeq_le_succ
    (c : ℝ) (M A B D Q : ℕ → ℝ) (Kcoef Hsource Winit : ℝ)
    (hc : 0 < c) (hB : ∀ k, 0 ≤ B k) (hD : ∀ k, 0 ≤ D k) (hQ : ∀ k, 0 ≤ Q k)
    (hKcoef : 0 ≤ Kcoef) (hHsource : 0 ≤ Hsource) (hWinit : 0 ≤ Winit) (k : ℕ) :
    spectatorIterationBudgetSeq c M A B D Q Kcoef Hsource Winit k ≤
      spectatorIterationBudgetSeq c M A B D Q Kcoef Hsource Winit (k+1) := by
  have hW := spectatorIterationBudgetSeq_nonneg c M A B D Q Kcoef Hsource Winit
    hc hB hD hQ hKcoef hHsource hWinit k
  exact (spectatorIterationBudget_bounds c (M k) (A k) (B k) (D k) (Q k)
    Kcoef Hsource k (spectatorIterationBudgetSeq c M A B D Q Kcoef Hsource Winit k)
    hc (hB k) (hD k) (hQ k) hKcoef hHsource hW).2.2.1

theorem spectatorIterationBudgetSeq_monotone
    (c : ℝ) (M A B D Q : ℕ → ℝ) (Kcoef Hsource Winit : ℝ)
    (hc : 0 < c) (hB : ∀ k, 0 ≤ B k) (hD : ∀ k, 0 ≤ D k) (hQ : ∀ k, 0 ≤ Q k)
    (hKcoef : 0 ≤ Kcoef) (hHsource : 0 ≤ Hsource) (hWinit : 0 ≤ Winit) :
    Monotone (spectatorIterationBudgetSeq c M A B D Q Kcoef Hsource Winit) :=
  monotone_nat_of_le_succ (spectatorIterationBudgetSeq_le_succ c M A B D Q Kcoef
    Hsource Winit hc hB hD hQ hKcoef hHsource hWinit)

#print axioms spectatorIterationBudgetSeq
#print axioms spectatorIterationBudgetSeq_nonneg
#print axioms spectatorIterationBudgetSeq_le_succ
#print axioms spectatorIterationBudgetSeq_monotone
end TheoremT.Continuum.WeakGrushin
