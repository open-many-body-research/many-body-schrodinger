import GrushinWordSplitCoordinateCount_v1

/-! Indexed functional R16 with exact ordered Leibniz multiplicities.
The coefficient family q is explicit and only finitely many bounds are
used. Genuine derivative identification of q and d remains an application
of the separate weak product calculus. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_potential_word_error_L2
    {μ : Measure (Space (Fin 3))} (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℕ → ℝ) (hN0 : ∀ k, 0 ≤ N k)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ k, k ≤ r-1 → ∀ a b, factorialMultiDerivativeCost a b ≤ k → factorialOuterNorm (W a b) ≤ N k)
    (q : List (Fin 4 ⊕ Fin 3) → Space (Fin 3) → ℝ)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hq : ∀ v, v.length ≤ r → AEStronglyMeasurable (q v) μ)
    (hqb : ∀ v, v.length ≤ r → ∀ᵐ p ∂μ, |q v p| ≤ M*A^v.length*(v.length.factorial : ℝ))
    (w : List (Fin 4 ⊕ Fin 3))
    (hc : factorialMultiDerivativeCost (factorialWordYCount w) (factorialWordTCount w) ≤ r) :
    ∃ H : Lp ℂ 2 μ,
      H =ᵐ[μ] (fun p => ((spectatorWordProperSplits w).map (fun ab =>
        q ab.1 p • d (factorialWordYCount ab.2) (factorialWordTCount ab.2) p)).sum) ∧
      ‖H‖ ≤ M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
        ((j+1).factorial : ℝ)*N (r-(j+1))) := by
  have hwlen : w.length ≤ r := by
    have ht := factorialDerivativeCost_total_le (∑ i, factorialWordYCount w i) (∑ j, factorialWordTCount w j)
    rw [factorialWordCounts_length] at ht
    unfold factorialMultiDerivativeCost at hc
    omega
  let F : ℕ → ℝ := fun j => M*A^j*(j.factorial : ℝ)*N (r-j)
  have hF : ∀ j, 0 ≤ F j := by
    intro j
    have hn := hN0 (r-j)
    dsimp [F]
    positivity
  have hterms (ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3))
      (hab : ab ∈ spectatorWordProperSplits w) :
      ∃ U : Lp ℂ 2 μ,
        U =ᵐ[μ] (fun p => q ab.1 p • d (factorialWordYCount ab.2) (factorialWordTCount ab.2) p) ∧
        ‖U‖ ≤ F ab.1.length := by
    have hs := spectatorWordProperSplits_strict hab
    have hall : ab ∈ spectatorWordSplits w := by
      rw [spectatorWordSplits_eq_proper_append]
      exact List.mem_append_left _ hab
    have hleft : ab.1.length ≤ r := by omega
    have hk : r-ab.1.length ≤ r-1 := by omega
    have hloss := factorialWordSplits_cost_loss hall
    have hcost : factorialMultiDerivativeCost (factorialWordYCount ab.2) (factorialWordTCount ab.2) ≤ r-ab.1.length := by omega
    obtain ⟨U,hU,hUn⟩ := factorial_unweighted_component_L2 d W (r-ab.1.length) (N (r-ab.1.length))
      (fun a b ha => hW a b (ha.trans hk)) (hN _ hk) _ _ hcost
    let K : ℝ := M*A^ab.1.length*(ab.1.length.factorial : ℝ)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hqn : ∀ᵐ p ∂μ, ‖q ab.1 p‖ ≤ K := by simpa only [Real.norm_eq_abs] using hqb ab.1 hleft
    have htop : MemLp (q ab.1) ⊤ μ := memLp_top_of_bound (hq ab.1 hleft) K hqn
    refine ⟨measureBoundedRealMul (q ab.1) htop U,?_,
      (measureBoundedRealMul_norm_le (q ab.1) htop hqn U).trans (mul_le_mul_of_nonneg_left hUn hK)⟩
    filter_upwards [measureBoundedRealMul_ae (q ab.1) htop U,hU] with p hp hu
    rw [hp,hu]
  have hex (ab : List (Fin 4 ⊕ Fin 3) × List (Fin 4 ⊕ Fin 3)) :
      ∃ U : Lp ℂ 2 μ, ab ∈ spectatorWordProperSplits w →
        U =ᵐ[μ] (fun p => q ab.1 p • d (factorialWordYCount ab.2) (factorialWordTCount ab.2) p) ∧
        ‖U‖ ≤ F ab.1.length := by
    by_cases hab : ab ∈ spectatorWordProperSplits w
    · obtain ⟨U,hU⟩ := hterms ab hab
      exact ⟨U,fun _ => hU⟩
    · exact ⟨0,fun h => False.elim (hab h)⟩
  choose U hU using hex
  obtain ⟨H,hH,hHn⟩ := factorial_word_proper_binomial_L2_bound w r hwlen U _
    (fun ab hab => (hU ab hab).1) F hF (fun ab hab => (hU ab hab).2)
  refine ⟨H,hH,hHn.trans_eq ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [F]
  ring

end TheoremT.Continuum.WeakGrushin
