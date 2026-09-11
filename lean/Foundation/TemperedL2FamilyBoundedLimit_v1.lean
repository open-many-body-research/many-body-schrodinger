import TemperedL2BoundedLimit_v1
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Simultaneous actual L2 outputs at a strong input limit with preservation of one
aggregate sum-of-squares bound. Applying Banach-Alaoglu/Riesz once on the Hilbert
finite product avoids multiplying the estimate by the number of components.
-/
noncomputable section
open MeasureTheory Filter TemperedDistribution LineDeriv
open scoped SchwartzMap LineDeriv Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem tempered_operator_family_l2_of_bounded_strong_approximation
    {ι : Type*} [Fintype ι] (A : ι → 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ))
    (u : ℕ → Lp ℂ 2 (volume : Measure E)) (d : ℕ → ι → Lp ℂ 2 (volume : Measure E))
    (f : Lp ℂ 2 (volume : Measure E)) (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n i, A i (u n : 𝓢'(E,ℂ)) = (d n i : 𝓢'(E,ℂ)))
    {C : ℝ} (hb : ∀ n, (∑ i, ‖d n i‖^2) ≤ C) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), (∑ i, ‖g i‖^2) ≤ C ∧
      ∀ i, A i (f : 𝓢'(E,ℂ)) = (g i : 𝓢'(E,ℂ)) := by
  let H := PiLp 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E))
  let D (n : ℕ) : H := WithLp.toLp 2 (d n)
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun i _ => sq_nonneg ‖d 0 i‖)).trans (hb 0)
  have hD : ∀ n, ‖D n‖ ≤ Real.sqrt C := by
    intro n
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, Real.sq_sqrt hC]
    exact hb n
  obtain ⟨g,hg,hlimit⟩ := hilbert_exists_bounded_vector_of_functional_limits D hD
  have hgsq : (∑ i, ‖g i‖^2) ≤ C := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hg
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)) g]
    simpa only [Real.sq_sqrt hC] using hh
  refine ⟨fun i => g i,hgsq,?_⟩
  intro i
  ext φ
  let J := Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2
  let V := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ
  let L : StrongDual ℂ H := (V.comp J).comp (PiLp.proj 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)) i)
  have ht : Tendsto (fun n => V (A i (J (u n)))) atTop (𝓝 (V (A i (J f)))) :=
    ((V.comp ((A i).comp J)).continuous.tendsto f).comp hf
  have he (n : ℕ) : V (A i (J (u n))) = L (D n) := by
    change (A i (u n : 𝓢'(E,ℂ))) φ = (d n i : 𝓢'(E,ℂ)) φ
    rw [hd n i]
  have hh := hlimit L (V (A i (J f))) (by simpa only [he] using ht)
  exact hh.symm

theorem weakL2Directional_family_of_bounded_strong_approximation
    {ι : Type*} [Fintype ι] (v : ι → E)
    (u : ℕ → Lp ℂ 2 (volume : Measure E)) (d : ℕ → ι → Lp ℂ 2 (volume : Measure E))
    (f : Lp ℂ 2 (volume : Measure E)) (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n i, WeakL2Directional (u n) (d n i) (v i))
    {C : ℝ} (hb : ∀ n, (∑ i, ‖d n i‖^2) ≤ C) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), (∑ i, ‖g i‖^2) ≤ C ∧
      ∀ i, WeakL2Directional f (g i) (v i) := by
  obtain ⟨g,hg,he⟩ := tempered_operator_family_l2_of_bounded_strong_approximation
    (fun i => lineDerivOpCLM ℂ 𝓢'(E,ℂ) (v i)) u d f hf
    (fun n i => distribution_directional_of_weakL2Directional (hd n i)) hb
  exact ⟨g,hg,fun i => weakL2Directional_of_distribution (he i)⟩

#print axioms tempered_operator_family_l2_of_bounded_strong_approximation
#print axioms weakL2Directional_family_of_bounded_strong_approximation
end TheoremT.Continuum
