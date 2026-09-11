import GenericWeakEllipticGain_v1

/-! Negative-order elliptic bootstrap, using the actual tempered Laplacian.
In particular, an L² function whose Laplacian is an L² function plus a finite
sum of directional derivatives of L² functions has genuine weak first
derivatives in every direction. No weak first derivative is an input.
This is the global algebraic step needed for a local two-cutoff bootstrap;
the local cutoff distribution identity is a separate obligation. -/

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv

namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memSobolev_gain_two_of_laplacian
    {s : ℝ} {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) :
    MemSobolev (s + 2) 2 u := by
  have h : MemSobolev s 2 (besselPotential E ℂ 2 u) := by
    rw [besselPotential_two_eq_sub_laplacian]
    have hc := hΔ.smul (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹))
    simpa only [Complex.coe_smul] using hu.sub hc
  simpa only [add_comm 2 s] using memSobolev_besselPotential_iff.mp h

theorem memSobolev_finite_sum {ι : Type*} {s : ℝ}
    (S : Finset ι) (u : ι → 𝓢'(E, ℂ))
    (hu : ∀ i ∈ S, MemSobolev s 2 (u i)) :
    MemSobolev s 2 (∑ i ∈ S, u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem memSobolev_one_of_l2_laplacian_divergence
    {ι : Type*} [Fintype ι] (v : ι → E)
    (u a : Lp ℂ 2 (volume : Measure E))
    (b : ι → Lp ℂ 2 (volume : Measure E))
    (hΔ : Δ (u : 𝓢'(E, ℂ)) =
      (a : 𝓢'(E, ℂ)) + ∑ i, ∂_{v i} (b i : 𝓢'(E, ℂ))) :
    MemSobolev 1 2 (u : 𝓢'(E, ℂ)) := by
  have hu0 : MemSobolev 0 2 (u : 𝓢'(E, ℂ)) :=
    memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have ha0 : MemSobolev 0 2 (a : 𝓢'(E, ℂ)) :=
    memSobolev_zero_iff.mpr ⟨a, rfl⟩
  have hbm (i : ι) : MemSobolev (-1) 2 (∂_{v i} (b i : 𝓢'(E, ℂ))) := by
    have hb0 : MemSobolev 0 2 (b i : 𝓢'(E, ℂ)) :=
      memSobolev_zero_iff.mpr ⟨b i, rfl⟩
    simpa using hb0.lineDerivOp (m := v i)
  have hd : MemSobolev (-1) 2 (Δ (u : 𝓢'(E, ℂ))) := by
    rw [hΔ]
    exact (ha0.mono (by norm_num)).add
      (memSobolev_finite_sum Finset.univ _ (fun i _ => hbm i))
  convert memSobolev_gain_two_of_laplacian
    (hu0.mono (show (-1 : ℝ) ≤ 0 by norm_num)) hd
    using 1 <;> norm_num

theorem weakL2_first_jets_of_l2_laplacian_divergence
    {ι : Type*} [Fintype ι] (v : ι → E)
    (u a : Lp ℂ 2 (volume : Measure E))
    (b : ι → Lp ℂ 2 (volume : Measure E))
    (hΔ : Δ (u : 𝓢'(E, ℂ)) =
      (a : 𝓢'(E, ℂ)) + ∑ i, ∂_{v i} (b i : 𝓢'(E, ℂ))) :
    ∃ d : E → Lp ℂ 2 (volume : Measure E),
      ∀ q, WeakL2Directional u (d q) q := by
  have h1 := hasWeakL2Order_of_memSobolev_nat (n := 1) u
    (by simpa only [Nat.cast_one] using
      memSobolev_one_of_l2_laplacian_divergence v u a b hΔ)
  obtain ⟨d, hd, _⟩ := h1
  exact ⟨d, hd⟩

#print axioms memSobolev_gain_two_of_laplacian
#print axioms memSobolev_finite_sum
#print axioms memSobolev_one_of_l2_laplacian_divergence
#print axioms weakL2_first_jets_of_l2_laplacian_divergence

end TheoremT.Continuum
