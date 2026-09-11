import TemperedL2FamilyBoundedLimit_v1

noncomputable section
open MeasureTheory Filter TemperedDistribution LineDeriv
open scoped SchwartzMap LineDeriv Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weakL2_anisotropic_jets_of_bounded_strong_approximation
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → E) (w : κ → E)
    (u : ℕ → Lp ℂ 2 (volume : Measure E))
    (dy : ℕ → ι → Lp ℂ 2 (volume : Measure E))
    (dt : ℕ → κ → Lp ℂ 2 (volume : Measure E))
    (eyy : ℕ → ι → ι → Lp ℂ 2 (volume : Measure E))
    (f : Lp ℂ 2 (volume : Measure E)) (hf : Tendsto u atTop (𝓝 f))
    (hdy : ∀ n i, WeakL2Directional (u n) (dy n i) (v i))
    (hdt : ∀ n j, WeakL2Directional (u n) (dt n j) (w j))
    (heyy : ∀ n i j, WeakL2Directional (dy n i) (eyy n i j) (v j))
    {C : ℝ} (hb : ∀ n, (∑ i, ‖dy n i‖^2) + (∑ j, ‖dt n j‖^2) +
      (∑ i, ∑ j, ‖eyy n i j‖^2) ≤ C) :
    ∃ gy : ι → Lp ℂ 2 (volume : Measure E),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure E),
    ∃ hyy : ι → ι → Lp ℂ 2 (volume : Measure E),
      ((∑ i, ‖gy i‖^2) + (∑ j, ‖gt j‖^2) + (∑ i, ∑ j, ‖hyy i j‖^2) ≤ C) ∧
      (∀ i, WeakL2Directional f (gy i) (v i)) ∧
      (∀ j, WeakL2Directional f (gt j) (w j)) ∧
      ∀ i j, WeakL2Directional (gy i) (hyy i j) (v j) := by
  classical
  let Dy (i : ι) := lineDerivOpCLM ℂ 𝓢'(E,ℂ) (v i)
  let Dt (j : κ) := lineDerivOpCLM ℂ 𝓢'(E,ℂ) (w j)
  let A : ((ι ⊕ κ) ⊕ (ι × ι)) → 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ) :=
    Sum.elim (Sum.elim Dy Dt) (fun ij => (Dy ij.2).comp (Dy ij.1))
  let out (n : ℕ) : ((ι ⊕ κ) ⊕ (ι × ι)) → Lp ℂ 2 (volume : Measure E) :=
    Sum.elim (Sum.elim (dy n) (dt n)) (fun ij => eyy n ij.1 ij.2)
  have hA (n : ℕ) (k : ((ι ⊕ κ) ⊕ (ι × ι))) :
      A k (u n : 𝓢'(E,ℂ)) = (out n k : 𝓢'(E,ℂ)) := by
    cases k with
    | inl k =>
      cases k with
      | inl i => exact distribution_directional_of_weakL2Directional (hdy n i)
      | inr j => exact distribution_directional_of_weakL2Directional (hdt n j)
    | inr ij =>
      change ∂_{v ij.2} (∂_{v ij.1} (u n : 𝓢'(E,ℂ))) = (eyy n ij.1 ij.2 : 𝓢'(E,ℂ))
      rw [distribution_directional_of_weakL2Directional (hdy n ij.1)]
      exact distribution_directional_of_weakL2Directional (heyy n ij.1 ij.2)
  have hbound (n : ℕ) : (∑ k, ‖out n k‖^2) ≤ C := by
    simpa only [Fintype.sum_sum_type,Fintype.sum_prod_type,out,Sum.elim_inl,Sum.elim_inr] using hb n
  obtain ⟨g,hg,hAg⟩ := tempered_operator_family_l2_of_bounded_strong_approximation A u out f hf hA hbound
  refine ⟨(fun i => g (.inl (.inl i))), (fun j => g (.inl (.inr j))),
    (fun i j => g (.inr (i,j))), ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.sum_sum_type,Fintype.sum_prod_type] using hg
  · intro i
    exact weakL2Directional_of_distribution (hAg (.inl (.inl i)))
  · intro j
    exact weakL2Directional_of_distribution (hAg (.inl (.inr j)))
  · intro i j
    apply weakL2Directional_of_distribution
    have hfirst := hAg (.inl (.inl i))
    have hsecond := hAg (.inr (i,j))
    change ∂_{v i} (f : 𝓢'(E,ℂ)) = (g (.inl (.inl i)) : 𝓢'(E,ℂ)) at hfirst
    change ∂_{v j} (∂_{v i} (f : 𝓢'(E,ℂ))) = (g (.inr (i,j)) : 𝓢'(E,ℂ)) at hsecond
    rwa [hfirst] at hsecond

#print axioms weakL2_anisotropic_jets_of_bounded_strong_approximation
end TheoremT.Continuum
