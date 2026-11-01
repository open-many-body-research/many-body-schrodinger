import SpectatorWordSplits_v1
import Mathlib.Data.Nat.Choose.Sum

/-! Exact grouping of ordered Leibniz choices by the number of derivatives
falling on the coefficient. Repeated directions retain their multiplicity.
This is the binomial factor used in R16, rather than a crude 2^order count. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem spectatorWordSplits_length_weight_sum {κ : Type} (w : List κ) (F : ℕ → ℝ) :
    ((spectatorWordSplits w).map (fun ab => F ab.1.length)).sum =
      ∑ j ∈ Finset.range (w.length+1), (w.length.choose j : ℝ)*F j := by
  induction w generalizing F with
  | nil => simp [spectatorWordSplits]
  | cons i w ih =>
    simp only [spectatorWordSplits,List.map_append,List.sum_append,List.map_map,
      Function.comp_def,List.length_cons]
    rw [ih (fun j => F (j+1)),ih F]
    rw [show w.length+1+1 = w.length+2 by omega]
    simpa only [add_comm] using (Finset.sum_choose_succ_mul (fun j _ => F j) w.length).symm

theorem spectatorWordProperSplits_length_weight_sum {κ : Type} (w : List κ) (F : ℕ → ℝ) :
    ((spectatorWordProperSplits w).map (fun ab => F ab.1.length)).sum =
      ∑ j ∈ Finset.range w.length, (w.length.choose (j+1) : ℝ)*F (j+1) := by
  have hs := spectatorWordSplits_length_weight_sum w F
  rw [spectatorWordSplits_eq_proper_append] at hs
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,List.length_nil,add_zero] at hs
  rw [Finset.sum_range_succ'] at hs
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul] at hs
  exact add_right_cancel hs

theorem spectatorWordProperSplits_length_weight_sum_le {κ : Type} (w : List κ)
    (r : ℕ) (hr : w.length ≤ r) (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ((spectatorWordProperSplits w).map (fun ab => F ab.1.length)).sum ≤
      ∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*F (j+1) := by
  rw [spectatorWordProperSplits_length_weight_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range w.length, (r.choose (j+1) : ℝ)*F (j+1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hF _)
      exact_mod_cast Nat.choose_le_choose (j+1) hr
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr)
      (fun j hj hnot => mul_nonneg (Nat.cast_nonneg _) (hF _))

end TheoremT.Continuum.WeakGrushin
