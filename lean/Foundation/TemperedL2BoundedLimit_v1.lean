import HilbertBoundedFunctionalLimits_v1
import GenericDistributionDirectionalConverse_v1

/-!
A bounded sequence of genuine L2 outputs of a continuous tempered operator has
an L2 output at every strong L2 input limit, with the same norm bound. The final
directional corollary uses the actual weak compact-test derivative definition.
-/
noncomputable section
open MeasureTheory Filter TemperedDistribution LineDeriv
open scoped SchwartzMap LineDeriv Topology
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem tempered_operator_l2_of_bounded_strong_approximation
    (A : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ))
    (u d : ℕ → Lp ℂ 2 (volume : Measure E)) (f : Lp ℂ 2 (volume : Measure E))
    (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n, A (u n : 𝓢'(E,ℂ)) = (d n : 𝓢'(E,ℂ)))
    {C : ℝ} (hb : ∀ n, ‖d n‖ ≤ C) :
    ∃ g : Lp ℂ 2 (volume : Measure E), ‖g‖ ≤ C ∧ A (f : 𝓢'(E,ℂ)) = (g : 𝓢'(E,ℂ)) := by
  obtain ⟨g,hg,hlimit⟩ := hilbert_exists_bounded_vector_of_functional_limits d hb
  refine ⟨g,hg,?_⟩
  ext φ
  let J := Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2
  let V := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ
  let L : StrongDual ℂ (Lp ℂ 2 (volume : Measure E)) := V.comp J
  have ht : Tendsto (fun n => V (A (J (u n)))) atTop (𝓝 (V (A (J f)))) :=
    ((V.comp (A.comp J)).continuous.tendsto f).comp hf
  have he (n : ℕ) : V (A (J (u n))) = L (d n) := by
    change (A (u n : 𝓢'(E,ℂ))) φ = (d n : 𝓢'(E,ℂ)) φ
    rw [hd n]
  have hh := hlimit L (V (A (J f))) (by simpa only [he] using ht)
  exact hh.symm

theorem weakL2Directional_of_bounded_strong_approximation
    (u d : ℕ → Lp ℂ 2 (volume : Measure E)) (f : Lp ℂ 2 (volume : Measure E)) (v : E)
    (hf : Tendsto u atTop (𝓝 f)) (hd : ∀ n, WeakL2Directional (u n) (d n) v)
    {C : ℝ} (hb : ∀ n, ‖d n‖ ≤ C) :
    ∃ g : Lp ℂ 2 (volume : Measure E), ‖g‖ ≤ C ∧ WeakL2Directional f g v := by
  obtain ⟨g,hg,he⟩ := tempered_operator_l2_of_bounded_strong_approximation
    (lineDerivOpCLM ℂ 𝓢'(E,ℂ) v) u d f hf
    (fun n => distribution_directional_of_weakL2Directional (hd n)) hb
  exact ⟨g,hg,weakL2Directional_of_distribution he⟩

#print axioms tempered_operator_l2_of_bounded_strong_approximation
#print axioms weakL2Directional_of_bounded_strong_approximation
end TheoremT.Continuum
