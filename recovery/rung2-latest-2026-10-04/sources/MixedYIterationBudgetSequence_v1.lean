import MixedYIterationBudget_v1
import Mathlib.Order.Monotone.Basic

/-! Stage-dependent explicit budgets for finite Y recovery. The recurrence
uses the actual single-stage constructor. Positivity and monotonicity only
concern these norm budgets and do not provide analytic gain premises. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

def mixedYIterationBudgetSeq (c : ℝ) (M A L D Q : ℕ → ℝ)
    (K0 Q0 H0 : ℝ) (m d : ℕ) (Winit : ℝ) : ℕ → ℝ
  | 0 => Winit
  | k+1 => mixedYIterationNext c (M k) (A k) (L k) (D k) (Q k) K0 Q0 H0 m d
      (mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m d Winit k)

theorem mixedYIterationBudgetSeq_nonneg
    (c : ℝ) (M A L D Q : ℕ → ℝ) (K0 Q0 H0 : ℝ) (m d : ℕ)
    {Winit : ℝ} (hWinit : 0 ≤ Winit) :
    ∀ k, 0 ≤ mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m d Winit k := by
  intro k
  induction k with
  | zero => exact hWinit
  | succ k ih =>
    exact mixedYIterationNext_nonneg c (M k) (A k) (L k) (D k) (Q k)
      K0 Q0 H0 m d _ ih

theorem mixedYIterationBudgetSeq_le_succ
    (c : ℝ) (M A L D Q : ℕ → ℝ) (K0 Q0 H0 : ℝ) (m d : ℕ) (Winit : ℝ) (k : ℕ) :
    mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m d Winit k ≤
      mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m d Winit (k+1) :=
  mixedYIterationNext_ge c (M k) (A k) (L k) (D k) (Q k) K0 Q0 H0 m d _

theorem mixedYIterationBudgetSeq_monotone
    (c : ℝ) (M A L D Q : ℕ → ℝ) (K0 Q0 H0 : ℝ) (m d : ℕ) (Winit : ℝ) :
    Monotone (mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m d Winit) :=
  monotone_nat_of_le_succ
    (mixedYIterationBudgetSeq_le_succ c M A L D Q K0 Q0 H0 m d Winit)

#print axioms mixedYIterationBudgetSeq
#print axioms mixedYIterationBudgetSeq_nonneg
#print axioms mixedYIterationBudgetSeq_le_succ
#print axioms mixedYIterationBudgetSeq_monotone
end TheoremT.Continuum.WeakGrushin
