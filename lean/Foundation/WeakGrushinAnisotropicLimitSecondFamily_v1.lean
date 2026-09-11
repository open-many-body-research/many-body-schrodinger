import TemperedL2FamilyBoundedLimit_v1
import ProductDistributionDirectionalConverse_v2

/-! Preservation of a separate ordered-second-derivative family bound under
strong L2 input convergence. The supplied first derivatives of the limit are
genuine weak derivatives, not assumptions on convergence of the approximating
derivative families. No bound on the approximating first derivatives is needed.
-/
noncomputable section
open MeasureTheory Filter TemperedDistribution LineDeriv
open scoped SchwartzMap LineDeriv Topology BigOperators
namespace TheoremT.Continuum

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2_second_family_of_bounded_strong_approximation
    {ι : Type*} [Fintype ι] (v : ι → Y × T)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (d : ℕ → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (e : ℕ → ι → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n i, WeakProductL2Directional (u n) (d n i) (v i))
    (he : ∀ n i j, WeakProductL2Directional (d n i) (e n i j) (v j))
    (g : ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (hg : ∀ i, WeakProductL2Directional f (g i) (v i))
    {C : ℝ} (hb : ∀ n, (∑ i, ∑ j, ‖e n i j‖^2) ≤ C) :
    ∃ h : ι → ι → Lp ℂ 2 (volume : Measure (Y × T)),
      (∑ i, ∑ j, ‖h i j‖^2) ≤ C ∧
      ∀ i j, WeakProductL2Directional (g i) (h i j) (v j) := by
  classical
  let D (i : ι) := lineDerivOpCLM ℂ 𝓢'(WithLp 2 (Y × T),ℂ) (WithLp.toLp 2 (v i))
  let A : (ι × ι) → 𝓢'(WithLp 2 (Y × T),ℂ) →L[ℂ] 𝓢'(WithLp 2 (Y × T),ℂ) :=
    fun ij => (D ij.2).comp (D ij.1)
  let out (n : ℕ) : (ι × ι) → Lp ℂ 2 (volume : Measure (WithLp 2 (Y × T))) :=
    fun ij => productEuclideanLift (e n ij.1 ij.2)
  have hlf : Tendsto (fun n => productEuclideanLift (u n)) atTop
      (𝓝 (productEuclideanLift f)) :=
    (productEuclideanLift.continuous.tendsto f).comp hf
  have hA (n : ℕ) (ij : ι × ι) :
      A ij (productEuclideanLift (u n) : 𝓢'(WithLp 2 (Y × T),ℂ)) =
        (out n ij : 𝓢'(WithLp 2 (Y × T),ℂ)) := by
    change ∂_{WithLp.toLp 2 (v ij.2)}
      (∂_{WithLp.toLp 2 (v ij.1)} (productEuclideanLift (u n) : 𝓢'(WithLp 2 (Y × T),ℂ))) =
        (productEuclideanLift (e n ij.1 ij.2) : 𝓢'(WithLp 2 (Y × T),ℂ))
    rw [distribution_directional_of_weakProductL2Directional (hd n ij.1)]
    exact distribution_directional_of_weakProductL2Directional (he n ij.1 ij.2)
  have hbound (n : ℕ) : (∑ ij, ‖out n ij‖^2) ≤ C := by
    simpa only [Fintype.sum_prod_type,out,LinearIsometry.norm_map] using hb n
  obtain ⟨H,hH,hAH⟩ := tempered_operator_family_l2_of_bounded_strong_approximation
    A (fun n => productEuclideanLift (u n)) out (productEuclideanLift f) hlf hA hbound
  refine ⟨(fun i j => productEuclideanUnlift (H (i,j))), ?_, ?_⟩
  · simpa only [Fintype.sum_prod_type,LinearIsometry.norm_map] using hH
  · intro i j
    have hsecond := hAH (i,j)
    change ∂_{WithLp.toLp 2 (v j)}
      (∂_{WithLp.toLp 2 (v i)} (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T),ℂ))) =
        (H (i,j) : 𝓢'(WithLp 2 (Y × T),ℂ)) at hsecond
    rw [distribution_directional_of_weakProductL2Directional (hg i)] at hsecond
    have hweak := weakProductL2Directional_of_euclidean (weakL2Directional_of_distribution hsecond)
    simpa only [productEuclideanUnlift_lift] using hweak

#print axioms weakProductL2_second_family_of_bounded_strong_approximation
end TheoremT.Continuum
