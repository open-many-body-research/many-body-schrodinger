import GrushinWordSplitBinomialNorm_v1
import CoordinateMultiIndexWord_v1

/-! Coordinate-count conservation for each actual ordered Leibniz split.
These identities connect the ordered word calculus to the natural-index
R6 cost without assuming that a chosen subword has a desired multiindex. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem spectatorWordSplits_countP {κ : Type} (p : κ → Bool) {w : List κ}
    {ab : List κ × List κ} (hab : ab ∈ spectatorWordSplits w) :
    ab.1.countP p+ab.2.countP p = w.countP p := by
  induction w generalizing ab with
  | nil =>
    have he : ab=([],[]) := by simpa [spectatorWordSplits] using hab
    simp [he]
  | cons x w ih =>
    simp only [spectatorWordSplits,List.mem_append,List.mem_map] at hab
    rcases hab with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · have hh := ih hq
      simp only [List.countP_cons]
      split <;> omega
    · have hh := ih hq
      simp only [List.countP_cons]
      split <;> omega

theorem factorial_word_sum_coordinate_counts {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : List κ) : (∑ i, w.countP (fun j => decide (j=i))) = w.length := by
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [List.countP_cons,List.length_cons]
    have ht (i : κ) : (if decide (x=i) then 1 else 0) = (Pi.single x 1 : κ → ℕ) i := by
      by_cases hi : i=x
      · subst i; simp
      · simp [hi,Ne.symm hi]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_pi_single',Finset.mem_univ,ite_true]
    omega

def factorialWordYCount (w : List (Fin 4 ⊕ Fin 3)) : Fin 4 → ℕ :=
  fun i => coordinateWordCount (.inl i) w

def factorialWordTCount (w : List (Fin 4 ⊕ Fin 3)) : Fin 3 → ℕ :=
  fun j => coordinateWordCount (.inr j) w

theorem factorialWordCounts_length (w : List (Fin 4 ⊕ Fin 3)) :
    (∑ i, factorialWordYCount w i)+(∑ j, factorialWordTCount w j)=w.length := by
  simpa only [factorialWordYCount,factorialWordTCount,coordinateWordCount,Fintype.sum_sum_type] using
    factorial_word_sum_coordinate_counts w

theorem factorialWordSplits_counts {w : List (Fin 4 ⊕ Fin 3)}
    {ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3)} (hab : ab ∈ spectatorWordSplits w) :
    (∀ i, factorialWordYCount ab.1 i+factorialWordYCount ab.2 i=factorialWordYCount w i) ∧
    (∀ j, factorialWordTCount ab.1 j+factorialWordTCount ab.2 j=factorialWordTCount w j) := by
  constructor
  · intro i
    exact spectatorWordSplits_countP (fun j => decide (j=Sum.inl i)) hab
  · intro j
    exact spectatorWordSplits_countP (fun i => decide (i=Sum.inr j)) hab

theorem factorialWordSplits_cost_loss {w : List (Fin 4 ⊕ Fin 3)}
    {ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3)} (hab : ab ∈ spectatorWordSplits w) :
    factorialMultiDerivativeCost (factorialWordYCount ab.2) (factorialWordTCount ab.2)+ab.1.length ≤
      factorialMultiDerivativeCost (factorialWordYCount w) (factorialWordTCount w) := by
  obtain ⟨hy,ht⟩ := factorialWordSplits_counts hab
  have hyl : ∀ i, factorialWordYCount ab.1 i ≤ factorialWordYCount w i := by intro i; have := hy i; omega
  have htl : ∀ j, factorialWordTCount ab.1 j ≤ factorialWordTCount w j := by intro j; have := ht j; omega
  have hye : (fun i => factorialWordYCount w i-factorialWordYCount ab.1 i)=factorialWordYCount ab.2 := by
    funext i; have := hy i; omega
  have hte : (fun j => factorialWordTCount w j-factorialWordTCount ab.1 j)=factorialWordTCount ab.2 := by
    funext j; have := ht j; omega
  have h := factorialMultiDerivativeCost_remove (factorialWordYCount w) (factorialWordYCount ab.1)
    (factorialWordTCount w) (factorialWordTCount ab.1) hyl htl
  rwa [hye,hte,factorialWordCounts_length] at h

end TheoremT.Continuum.WeakGrushin
