import GrushinWordSplitBinomial_v1
import GrushinFactorialPotentialComponentL2_v1

/-! Norm summation for proper ordered Leibniz splits. Each positional
choice is counted, including choices that produce identical subwords. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_norm_list_map_sum_le {ι E : Type*} [SeminormedAddCommGroup E]
    (l : List ι) (U : ι → E) (F : ι → ℝ) (h : ∀ a ∈ l, ‖U a‖ ≤ F a) :
    ‖(l.map U).sum‖ ≤ (l.map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (h a (by simp))
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb))))

theorem factorial_lp_list_map_sum_ae {ι X : Type*} [MeasurableSpace X] {μ : Measure X}
    (l : List ι) (U : ι → Lp ℂ 2 μ) (f : ι → X → ℂ)
    (h : ∀ a ∈ l, U a =ᵐ[μ] f a) :
    (l.map U).sum =ᵐ[μ] (fun p => (l.map (fun a => f a p)).sum) := by
  induction l with
  | nil =>
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with p hp
    simpa only [List.map_nil,List.sum_nil,Pi.zero_apply] using hp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    filter_upwards [Lp.coeFn_add (U a) ((l.map U).sum),ha,hl] with p hp hpa hpl
    simp only [List.map_cons,List.sum_cons]
    rw [hp]
    change U a p+((l.map U).sum) p = _
    rw [hpa,hpl]

theorem factorial_word_proper_binomial_norm_bound {κ E : Type}
    [SeminormedAddCommGroup E] (w : List κ) (r : ℕ) (hr : w.length ≤ r)
    (U : List κ × List κ → E) (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j)
    (hU : ∀ ab ∈ spectatorWordProperSplits w, ‖U ab‖ ≤ F ab.1.length) :
    ‖((spectatorWordProperSplits w).map U).sum‖ ≤
      ∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*F (j+1) :=
  (factorial_norm_list_map_sum_le _ U _ hU).trans
    (spectatorWordProperSplits_length_weight_sum_le w r hr F hF)

theorem factorial_word_proper_binomial_L2_bound {κ X : Type} [MeasurableSpace X]
    {μ : Measure X} (w : List κ) (r : ℕ) (hr : w.length ≤ r)
    (U : List κ × List κ → Lp ℂ 2 μ) (f : List κ × List κ → X → ℂ)
    (hU : ∀ ab ∈ spectatorWordProperSplits w, U ab =ᵐ[μ] f ab)
    (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j)
    (hUn : ∀ ab ∈ spectatorWordProperSplits w, ‖U ab‖ ≤ F ab.1.length) :
    ∃ H : Lp ℂ 2 μ,
      H =ᵐ[μ] (fun p => ((spectatorWordProperSplits w).map (fun ab => f ab p)).sum) ∧
      ‖H‖ ≤ ∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*F (j+1) :=
  ⟨((spectatorWordProperSplits w).map U).sum,factorial_lp_list_map_sum_ae _ U f hU,
    factorial_word_proper_binomial_norm_bound w r hr U F hF hUn⟩

end TheoremT.Continuum.WeakGrushin
