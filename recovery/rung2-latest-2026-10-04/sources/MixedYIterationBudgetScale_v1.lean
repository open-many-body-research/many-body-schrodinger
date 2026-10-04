import MixedYIterationBudgetSequence_v1

/-! Finite Y budgets preserve a common nonnegative reference factor. Because
the stage constructor uses max, homogeneity explicitly requires a nonnegative
scale. No division by the reference factor or positivity away from zero is used. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

theorem mixedYSourceBudget_input_mono (c K Q : ℝ) (m d : ℕ)
    {H H' W W' : ℝ} (hH : H ≤ H') (hW : W ≤ W') :
    mixedYSourceBudget c K Q H m d W ≤ mixedYSourceBudget c K Q H' m d W' := by
  unfold mixedYSourceBudget
  gcongr

theorem mixedYIterationNext_input_mono
    (c M A L D Q K0 Q0 : ℝ) (m d : ℕ) {H H' W W' : ℝ}
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hH : H ≤ H') (hW : W ≤ W') :
    mixedYIterationNext c M A L D Q K0 Q0 H m d W ≤
      mixedYIterationNext c M A L D Q K0 Q0 H' m d W' := by
  have hS := mixedYSourceBudget_input_mono c K0 Q0 m d hH hW
  unfold mixedYIterationNext
  apply max_le_max hW
  gcongr

theorem mixedYIterationNext_scale
    (c M A L D Q K0 Q0 H W r : ℝ) (m d : ℕ) (hr : 0 ≤ r) :
    mixedYIterationNext c M A L D Q K0 Q0 (r*H) m d (r*W) =
      r*mixedYIterationNext c M A L D Q K0 Q0 H m d W := by
  unfold mixedYIterationNext
  rw [mul_max_of_nonneg _ _ hr]
  congr 1
  unfold mixedYSourceBudget
  ring

theorem mixedYIterationBudgetSeq_scale
    (c : ℝ) (M A L D Q : ℕ → ℝ) (K0 Q0 H W r : ℝ) (m d n : ℕ) (hr : 0 ≤ r) :
    mixedYIterationBudgetSeq c M A L D Q K0 Q0 (r*H) m d (r*W) n =
      r*mixedYIterationBudgetSeq c M A L D Q K0 Q0 H m d W n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mixedYIterationBudgetSeq,ih]
    exact mixedYIterationNext_scale c (M n) (A n) (L n) (D n) (Q n) K0 Q0 H
      (mixedYIterationBudgetSeq c M A L D Q K0 Q0 H m d W n) r m d hr

theorem mixedYIterationBudgetSeq_input_mono
    (c : ℝ) (M A L D Q : ℕ → ℝ) (K0 Q0 : ℝ) (m d : ℕ)
    {H H' W W' : ℝ} (hH : H ≤ H') (hW : W ≤ W') (n : ℕ) :
    (∀ k < n, 0 ≤ L k) → (∀ k < n, 0 ≤ D k) → (∀ k < n, 0 ≤ Q k) →
    mixedYIterationBudgetSeq c M A L D Q K0 Q0 H m d W n ≤
      mixedYIterationBudgetSeq c M A L D Q K0 Q0 H' m d W' n := by
  induction n with
  | zero => intro _ _ _; exact hW
  | succ n ih =>
    intro hL hD hQ
    apply mixedYIterationNext_input_mono c (M n) (A n) (L n) (D n) (Q n) K0 Q0 m d
      (hL n (by omega)) (hD n (by omega)) (hQ n (by omega)) hH
    exact ih (fun k hk => hL k (by omega)) (fun k hk => hD k (by omega))
      (fun k hk => hQ k (by omega))

theorem mixedYIterationBudgetSeq_common_bound
    (c : ℝ) (M A L D Q : ℕ → ℝ) (K0 Q0 : ℝ) (m d : ℕ)
    {H W Hbase Wbase r : ℝ} (hr : 0 ≤ r) (hH : H ≤ r*Hbase) (hW : W ≤ r*Wbase) (n : ℕ)
    (hL : ∀ k < n, 0 ≤ L k) (hD : ∀ k < n, 0 ≤ D k) (hQ : ∀ k < n, 0 ≤ Q k) :
    mixedYIterationBudgetSeq c M A L D Q K0 Q0 H m d W n ≤
      r*mixedYIterationBudgetSeq c M A L D Q K0 Q0 Hbase m d Wbase n := by
  exact (mixedYIterationBudgetSeq_input_mono c M A L D Q K0 Q0 m d hH hW n hL hD hQ).trans_eq
    (mixedYIterationBudgetSeq_scale c M A L D Q K0 Q0 Hbase Wbase r m d n hr)

#print axioms mixedYSourceBudget_input_mono
#print axioms mixedYIterationNext_input_mono
#print axioms mixedYIterationNext_scale
#print axioms mixedYIterationBudgetSeq_scale
#print axioms mixedYIterationBudgetSeq_input_mono
#print axioms mixedYIterationBudgetSeq_common_bound
end TheoremT.Continuum.WeakGrushin
