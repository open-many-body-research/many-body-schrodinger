import GenericBoundedSmoothMultiplier_v1
import GenericDistributionDirectionalConverse_v1

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_h2_of_h1_multiplier_divergence
    {ι : Type*} [Fintype ι] (v : ι → E)
    (u a f : Lp ℂ 2 (volume : Measure E))
    (d : E → Lp ℂ 2 (volume : Measure E))
    (hd : ∀ q, WeakL2Directional f (d q) q)
    (χ : ι → E → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hm : ∀ i, MemLp (χ i) ⊤ volume)
    (hDm : ∀ i, MemLp (fun x => fderiv ℝ (χ i) x (v i)) ⊤ volume)
    (hΔ : Δ (u : 𝓢'(E,ℂ)) = (a : 𝓢'(E,ℂ)) +
      ∑ i, ∂_{v i} (genericBoundedRealMul (χ i) (hm i) f : 𝓢'(E,ℂ))) :
    HasWeakL2Order u 2 := by
  let g (i : ι) := genericBoundedRealMul (χ i) (hm i) (d (v i)) +
    genericBoundedRealMul (fun x => fderiv ℝ (χ i) x (v i)) (hDm i) f
  have hg (i : ι) : ∂_{v i} (genericBoundedRealMul (χ i) (hm i) f : 𝓢'(E,ℂ)) =
      (g i : 𝓢'(E,ℂ)) :=
    distribution_directional_of_weakL2Directional
      (weakL2Directional_genericBoundedRealMul (hd (v i)) (χ i) (hχ i) (hm i) (hDm i))
  let w : Lp ℂ 2 (volume : Measure E) := a + ∑ i, g i
  have hw : (w : 𝓢'(E,ℂ)) = (a : 𝓢'(E,ℂ)) + ∑ i, (g i : 𝓢'(E,ℂ)) := by
    simp only [w,← Lp.toTemperedDistributionCLM_apply,map_add,map_sum]
  apply hasWeakL2Order_two_of_distribution_laplacian u w
  rw [hw,hΔ]
  simp_rw [hg]

#print axioms generic_h2_of_h1_multiplier_divergence
end TheoremT.Continuum
