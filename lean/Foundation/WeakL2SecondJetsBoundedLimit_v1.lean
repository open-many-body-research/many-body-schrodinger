import TemperedL2FamilyBoundedLimit_v1

/-!
Actual weak first and ordered second L2 derivative witnesses survive strong L2
input convergence when their combined squared norms are uniformly bounded.
No convergence of any derivative sequence is required or assumed.
-/
noncomputable section
open MeasureTheory Filter TemperedDistribution LineDeriv
open scoped SchwartzMap LineDeriv Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weakL2_second_jets_of_bounded_strong_approximation
    {ι : Type*} [Fintype ι] (v : ι → E)
    (u : ℕ → Lp ℂ 2 (volume : Measure E))
    (d : ℕ → ι → Lp ℂ 2 (volume : Measure E))
    (e : ℕ → ι → ι → Lp ℂ 2 (volume : Measure E))
    (f : Lp ℂ 2 (volume : Measure E)) (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n i, WeakL2Directional (u n) (d n i) (v i))
    (he : ∀ n i j, WeakL2Directional (d n i) (e n i j) (v j))
    {C : ℝ} (hb : ∀ n, (∑ i, ‖d n i‖^2) + (∑ i, ∑ j, ‖e n i j‖^2) ≤ C) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), ∃ h : ι → ι → Lp ℂ 2 (volume : Measure E),
      ((∑ i, ‖g i‖^2) + (∑ i, ∑ j, ‖h i j‖^2) ≤ C) ∧
      (∀ i, WeakL2Directional f (g i) (v i)) ∧
      ∀ i j, WeakL2Directional (g i) (h i j) (v j) := by
  classical
  let D (i : ι) := lineDerivOpCLM ℂ 𝓢'(E,ℂ) (v i)
  let A : (ι ⊕ (ι × ι)) → 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ) :=
    Sum.elim D (fun ij => (D ij.2).comp (D ij.1))
  let out (n : ℕ) : (ι ⊕ (ι × ι)) → Lp ℂ 2 (volume : Measure E) :=
    Sum.elim (d n) (fun ij => e n ij.1 ij.2)
  have hA (n : ℕ) (k : ι ⊕ (ι × ι)) : A k (u n : 𝓢'(E,ℂ)) = (out n k : 𝓢'(E,ℂ)) := by
    cases k with
    | inl i => exact distribution_directional_of_weakL2Directional (hd n i)
    | inr ij =>
      change ∂_{v ij.2} (∂_{v ij.1} (u n : 𝓢'(E,ℂ))) = (e n ij.1 ij.2 : 𝓢'(E,ℂ))
      rw [distribution_directional_of_weakL2Directional (hd n ij.1)]
      exact distribution_directional_of_weakL2Directional (he n ij.1 ij.2)
  have hbound (n : ℕ) : (∑ k, ‖out n k‖^2) ≤ C := by
    simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type, out, Sum.elim_inl, Sum.elim_inr] using hb n
  obtain ⟨G,hG,hAG⟩ := tempered_operator_family_l2_of_bounded_strong_approximation A u out f hf hA hbound
  refine ⟨(fun i => G (.inl i)), (fun i j => G (.inr (i,j))), ?_, ?_, ?_⟩
  · simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type] using hG
  · intro i
    exact weakL2Directional_of_distribution (hAG (.inl i))
  · intro i j
    apply weakL2Directional_of_distribution
    have hfirst := hAG (.inl i)
    have hsecond := hAG (.inr (i,j))
    change ∂_{v i} (f : 𝓢'(E,ℂ)) = (G (.inl i) : 𝓢'(E,ℂ)) at hfirst
    change ∂_{v j} (∂_{v i} (f : 𝓢'(E,ℂ))) = (G (.inr (i,j)) : 𝓢'(E,ℂ)) at hsecond
    rwa [hfirst] at hsecond

#print axioms weakL2_second_jets_of_bounded_strong_approximation
end TheoremT.Continuum
