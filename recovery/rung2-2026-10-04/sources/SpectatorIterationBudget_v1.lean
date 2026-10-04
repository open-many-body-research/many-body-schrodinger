import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Explicit squared budgets for the actual finite spectator iteration.
These are arithmetic consequences of the displayed one-stage derivative
estimates. They are not additional analytic estimates or complexity claims. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

def spectatorIterationJ (M A B D Q Kcoef Hsource : ℝ) (k : ℕ) (W : ℝ) : ℝ :=
  (4*A^2+16*B*(D/2+Q)+2*(2*M^2+8*B*D)*Kcoef^2)*W +
    2*(2*M^2+8*B*D)*(2*Hsource+2*(((2^k-1 : ℕ) : ℝ)^2)*Kcoef^2*W)

def spectatorIterationNext (c M A B D Q Kcoef Hsource : ℝ) (k : ℕ) (W : ℝ) : ℝ :=
  W+2*M^2*W+(9/4+1/(16*c))*spectatorIterationJ M A B D Q Kcoef Hsource k W

theorem spectatorIterationJ_nonneg
    (M A B D Q Kcoef Hsource : ℝ) (k : ℕ) (W : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hHsource : 0 ≤ Hsource) (hW : 0 ≤ W) :
    0 ≤ spectatorIterationJ M A B D Q Kcoef Hsource k W := by
  unfold spectatorIterationJ
  positivity

theorem spectatorIterationBudget_bounds
    (c M A B D Q Kcoef Hsource : ℝ) (k : ℕ) (W : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (_hKcoef : 0 ≤ Kcoef) (hHsource : 0 ≤ Hsource) (hW : 0 ≤ W) :
    let J := spectatorIterationJ M A B D Q Kcoef Hsource k W
    let Wnext := spectatorIterationNext c M A B D Q Kcoef Hsource k W
    0 ≤ J ∧ 0 ≤ Wnext ∧ W ≤ Wnext ∧
      2*M^2*W+(3/4 : ℝ)*J ≤ Wnext ∧
      J/(16*c) ≤ Wnext ∧ (3/2 : ℝ)*J ≤ Wnext := by
  have hJ := spectatorIterationJ_nonneg M A B D Q Kcoef Hsource k W
    hB hD hQ hHsource hW
  have hMW : 0 ≤ 2*M^2*W := by positivity
  have hTJ : 0 ≤ (1/(16*c))*spectatorIterationJ M A B D Q Kcoef Hsource k W :=
    mul_nonneg (by positivity) hJ
  have hdiv : spectatorIterationJ M A B D Q Kcoef Hsource k W/(16*c) =
      (1/(16*c))*spectatorIterationJ M A B D Q Kcoef Hsource k W := by ring
  dsimp only
  refine ⟨hJ,?_,?_,?_,?_,?_⟩
  · unfold spectatorIterationNext
    nlinarith
  · unfold spectatorIterationNext
    nlinarith
  · unfold spectatorIterationNext
    nlinarith
  · rw [hdiv]
    unfold spectatorIterationNext
    nlinarith
  · unfold spectatorIterationNext
    nlinarith

#print axioms spectatorIterationJ
#print axioms spectatorIterationNext
#print axioms spectatorIterationJ_nonneg
#print axioms spectatorIterationBudget_bounds
end TheoremT.Continuum.WeakGrushin
