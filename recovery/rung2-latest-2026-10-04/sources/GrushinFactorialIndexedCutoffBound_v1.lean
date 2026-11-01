import GrushinFactorialIndexRowBudget_v1

/-! The full indexed functional cutoff estimate underlying R13. Its
lower-order budgets use the exact R3 set and R6 cost, and all weighted
rows are constructed by proved index decompositions. The indexed family
d remains raw; this does not claim differential compatibility by fiat. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_indexed_cutoff_error_L2
    (a : Space (Fin 3)) (ha : a.1 = 0) (c : ℝ)
    {aY aT ρ s e C1 C2 : ℝ} (he : 0 < e) (hse : s+e ≤ ρ) (hρ : ρ < aY)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    {μ : Measure (Space (Fin 3))} (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (hr : 2 ≤ r) (N1 N2 : ℝ)
    (hW : ∀ α β, factorialMultiDerivativeCost α β ≤ r-1 →
      FactorialShiftedOuterL2Rep d W α β)
    (hN1 : ∀ α β, factorialMultiDerivativeCost α β ≤ r-1 → factorialOuterNorm (W α β) ≤ N1)
    (hN2 : ∀ α β, factorialMultiDerivativeCost α β ≤ r-2 → factorialOuterNorm (W α β) ≤ N2)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (hf : AEStronglyMeasurable (d α β) μ)
    (hgy : ∀ i, AEStronglyMeasurable (d (α+Pi.single i 1) β) μ) :
    ∃ H : Lp ℂ 2 μ,
      H =ᵐ[μ] rawGrushinCutoffError c (factorialRectCutoff a aY aT s e)
        (d α β) (fun i => d (α+Pi.single i 1) β) (fun j => d α (β+Pi.single j 1)) ∧
      ‖H‖ ≤ (((8/3 : ℝ)*C1)/e)*(8/(aY-ρ)^2+6*|c|)*N1+
        (((32/9 : ℝ)*(C2+C1^2))/e^2)*(4/(aY-ρ)^2+3*|c|)*N2 := by
  have hW2 : ∀ α β, factorialMultiDerivativeCost α β ≤ r-2 →
      FactorialShiftedOuterL2Rep d W α β := by
    intro α β h
    exact hW α β (by omega)
  obtain ⟨w0,hw0,hw0n⟩ := factorial_zero_row_budget d W r N2 hr hW2 hN2 α β hc
  choose wy hwy hwyn using fun i : Fin 4 =>
    factorial_first_y_row_budget d W r N1 (by omega) hW hN1 α β hc i
  choose wt hwt hwtn using fun j : Fin 3 =>
    factorial_first_t_row_budget d W r N1 (by omega) hW hN1 α β hc j
  exact factorial_raw_cutoff_error_L2 a ha c he hse hρ hC1 hC2 _ _ _ hf hgy
    w0 wy wt hw0 hwy hwt N1 N2 hw0n hwyn hwtn

end TheoremT.Continuum.WeakGrushin
