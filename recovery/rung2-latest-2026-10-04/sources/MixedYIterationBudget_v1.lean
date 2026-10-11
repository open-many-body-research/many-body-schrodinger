import SpectatorIterationState_v1

/-! Explicit finite source and Y-stage squared-norm budgets. These are
arithmetic constructors for the proved gain, with dimension and word-count
factors shown. They are not bit-complexity or implementation claims.
-/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

def mixedYSourceBudget (c K Q H : ℝ) (m d : ℕ) (W : ℝ) : ℝ :=
  3*H + 3*((2 : ℝ)^m)^2*K^2*W + 3*c^2*((2 : ℝ)^m)^2*(d : ℝ)^2*Q^2*W

def mixedYIterationNext (c M A L D Q K0 Q0 H0 : ℝ) (m d : ℕ) (W : ℝ) : ℝ :=
  max W ((3/2 : ℝ)*((4*A^2+16*L*(D/2+Q))*W+
    (2*M^2+8*L*D)*mixedYSourceBudget c K0 Q0 H0 m d W))

theorem mixedYSourceBudget_nonneg (c K Q H : ℝ) (m d : ℕ) (W : ℝ)
    (hH : 0 ≤ H) (hW : 0 ≤ W) : 0 ≤ mixedYSourceBudget c K Q H m d W := by
  unfold mixedYSourceBudget
  positivity

theorem mixedYIterationNext_ge (c M A L D Q K0 Q0 H0 : ℝ) (m d : ℕ) (W : ℝ) :
    W ≤ mixedYIterationNext c M A L D Q K0 Q0 H0 m d W := le_max_left _ _

theorem mixedYIterationNext_nonneg (c M A L D Q K0 Q0 H0 : ℝ) (m d : ℕ) (W : ℝ)
    (hW : 0 ≤ W) : 0 ≤ mixedYIterationNext c M A L D Q K0 Q0 H0 m d W :=
  hW.trans (mixedYIterationNext_ge c M A L D Q K0 Q0 H0 m d W)

#print axioms mixedYSourceBudget_nonneg
#print axioms mixedYIterationNext_ge
#print axioms mixedYIterationNext_nonneg
end TheoremT.Continuum.WeakGrushin
