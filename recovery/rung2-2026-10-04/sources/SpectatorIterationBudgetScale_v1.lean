import SpectatorIterationBudgetSequence_v1

/-! The actual finite squared-budget recurrence is linear under joint scaling
of its source and initial budgets, and monotone in these inputs. The finite
stage conditions suffice. This permits solution-independent constants after
factoring out a common reference integral; it supplies no analytic premise. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

theorem spectatorIterationJ_input_mono
    (M A B D Q K : ℝ) (k : ℕ) {H H' W W' : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hH : H ≤ H') (hW : W ≤ W') :
    spectatorIterationJ M A B D Q K H k W ≤
      spectatorIterationJ M A B D Q K H' k W' := by
  unfold spectatorIterationJ
  gcongr

theorem spectatorIterationNext_input_mono
    (c M A B D Q K : ℝ) (k : ℕ) {H H' W W' : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hH : H ≤ H') (hW : W ≤ W') :
    spectatorIterationNext c M A B D Q K H k W ≤
      spectatorIterationNext c M A B D Q K H' k W' := by
  have hJ := spectatorIterationJ_input_mono M A B D Q K k hB hD hQ hH hW
  unfold spectatorIterationNext
  exact add_le_add (add_le_add hW (mul_le_mul_of_nonneg_left hW (by positivity)))
    (mul_le_mul_of_nonneg_left hJ (by positivity))

theorem spectatorIterationNext_scale (c M A B D Q K H W r : ℝ) (k : ℕ) :
    spectatorIterationNext c M A B D Q K (r*H) k (r*W) =
      r * spectatorIterationNext c M A B D Q K H k W := by
  unfold spectatorIterationNext spectatorIterationJ
  ring

theorem spectatorIterationBudgetSeq_scale
    (c : ℝ) (M A B D Q : ℕ → ℝ) (K H W r : ℝ) (n : ℕ) :
    spectatorIterationBudgetSeq c M A B D Q K (r*H) (r*W) n =
      r * spectatorIterationBudgetSeq c M A B D Q K H W n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [spectatorIterationBudgetSeq, ih]
    exact spectatorIterationNext_scale c (M n) (A n) (B n) (D n) (Q n) K H
      (spectatorIterationBudgetSeq c M A B D Q K H W n) r n

theorem spectatorIterationBudgetSeq_input_mono
    (c : ℝ) (M A B D Q : ℕ → ℝ) (K : ℝ) {H H' W W' : ℝ}
    (hc : 0 < c) (hH : H ≤ H') (hW : W ≤ W') (n : ℕ) :
    (∀ k < n, 0 ≤ B k) → (∀ k < n, 0 ≤ D k) → (∀ k < n, 0 ≤ Q k) →
    spectatorIterationBudgetSeq c M A B D Q K H W n ≤
      spectatorIterationBudgetSeq c M A B D Q K H' W' n := by
  induction n with
  | zero => intro _ _ _; exact hW
  | succ n ih =>
    intro hB hD hQ
    apply spectatorIterationNext_input_mono c (M n) (A n) (B n) (D n) (Q n) K n hc
      (hB n (by omega)) (hD n (by omega)) (hQ n (by omega)) hH
    exact ih (fun k hk => hB k (by omega)) (fun k hk => hD k (by omega))
      (fun k hk => hQ k (by omega))

theorem spectatorIterationBudgetSeq_common_bound
    (c : ℝ) (M A B D Q : ℕ → ℝ) (K : ℝ) {H W Hbase Wbase r : ℝ}
    (hc : 0 < c) (hH : H ≤ r*Hbase) (hW : W ≤ r*Wbase) (n : ℕ)
    (hB : ∀ k < n, 0 ≤ B k) (hD : ∀ k < n, 0 ≤ D k) (hQ : ∀ k < n, 0 ≤ Q k) :
    spectatorIterationBudgetSeq c M A B D Q K H W n ≤
      r * spectatorIterationBudgetSeq c M A B D Q K Hbase Wbase n := by
  calc
    _ ≤ spectatorIterationBudgetSeq c M A B D Q K (r*Hbase) (r*Wbase) n :=
      spectatorIterationBudgetSeq_input_mono c M A B D Q K hc hH hW n hB hD hQ
    _ = _ := spectatorIterationBudgetSeq_scale c M A B D Q K Hbase Wbase r n

#print axioms spectatorIterationJ_input_mono
#print axioms spectatorIterationNext_input_mono
#print axioms spectatorIterationNext_scale
#print axioms spectatorIterationBudgetSeq_scale
#print axioms spectatorIterationBudgetSeq_input_mono
#print axioms spectatorIterationBudgetSeq_common_bound
end TheoremT.Continuum.WeakGrushin
