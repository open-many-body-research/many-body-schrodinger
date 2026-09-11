import WeakL2SecondJetsBoundedLimit_v1
import ProductWeakDirectionalBoundedLimit_v1

/-!
Strong L2 limits on the ordinary Cartesian product preserve one aggregate
squared-norm bound for finite families of genuine weak first derivatives and
ordered second derivatives. The Euclidean-copy lift and unlift are exact
isometries, so the constant is unchanged and no component-count factor occurs.
No convergence of the derivative sequences is a hypothesis.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2Directional_family_of_bounded_strong_approximation
    {ι : Type*} [Fintype ι] (v : ι → Y × T)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (d : ℕ → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n i, WeakProductL2Directional (u n) (d n i) (v i))
    {C : ℝ} (hb : ∀ n, (∑ i, ‖d n i‖^2) ≤ C) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure (Y × T)),
      (∑ i, ‖g i‖^2) ≤ C ∧ ∀ i, WeakProductL2Directional f (g i) (v i) := by
  have hlf : Tendsto (fun n => productEuclideanLift (u n)) atTop
      (𝓝 (productEuclideanLift f)) :=
    (productEuclideanLift.continuous.tendsto f).comp hf
  have hlb (n : ℕ) : (∑ i, ‖productEuclideanLift (d n i)‖^2) ≤ C := by
    simpa only [LinearIsometry.norm_map] using hb n
  obtain ⟨g,hg,hgD⟩ := weakL2Directional_family_of_bounded_strong_approximation
    (fun i => WithLp.toLp 2 (v i)) (fun n => productEuclideanLift (u n))
    (fun n i => productEuclideanLift (d n i)) (productEuclideanLift f) hlf
    (fun n i => weakL2Directional_productEuclideanLift (hd n i)) hlb
  refine ⟨fun i => productEuclideanUnlift (g i), ?_, ?_⟩
  · simpa only [LinearIsometry.norm_map] using hg
  · intro i
    have h := weakProductL2Directional_of_euclidean (hgD i)
    simpa only [productEuclideanUnlift_lift] using h

theorem weakProductL2_second_jets_of_bounded_strong_approximation
    {ι : Type*} [Fintype ι] (v : ι → Y × T)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (d : ℕ → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (e : ℕ → ι → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n i, WeakProductL2Directional (u n) (d n i) (v i))
    (he : ∀ n i j, WeakProductL2Directional (d n i) (e n i j) (v j))
    {C : ℝ} (hb : ∀ n, (∑ i, ‖d n i‖^2) + (∑ i, ∑ j, ‖e n i j‖^2) ≤ C) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ h : ι → ι → Lp ℂ 2 (volume : Measure (Y × T)),
      ((∑ i, ‖g i‖^2) + (∑ i, ∑ j, ‖h i j‖^2) ≤ C) ∧
      (∀ i, WeakProductL2Directional f (g i) (v i)) ∧
      ∀ i j, WeakProductL2Directional (g i) (h i j) (v j) := by
  have hlf : Tendsto (fun n => productEuclideanLift (u n)) atTop
      (𝓝 (productEuclideanLift f)) :=
    (productEuclideanLift.continuous.tendsto f).comp hf
  have hlb (n : ℕ) : (∑ i, ‖productEuclideanLift (d n i)‖^2) +
      (∑ i, ∑ j, ‖productEuclideanLift (e n i j)‖^2) ≤ C := by
    simpa only [LinearIsometry.norm_map] using hb n
  obtain ⟨g,h,hbound,hg,hh⟩ := weakL2_second_jets_of_bounded_strong_approximation
    (fun i => WithLp.toLp 2 (v i)) (fun n => productEuclideanLift (u n))
    (fun n i => productEuclideanLift (d n i))
    (fun n i j => productEuclideanLift (e n i j)) (productEuclideanLift f) hlf
    (fun n i => weakL2Directional_productEuclideanLift (hd n i))
    (fun n i j => weakL2Directional_productEuclideanLift (he n i j)) hlb
  refine ⟨(fun i => productEuclideanUnlift (g i)),
    (fun i j => productEuclideanUnlift (h i j)), ?_, ?_, ?_⟩
  · simpa only [LinearIsometry.norm_map] using hbound
  · intro i
    have hD := weakProductL2Directional_of_euclidean (hg i)
    simpa only [productEuclideanUnlift_lift] using hD
  · intro i j
    exact weakProductL2Directional_of_euclidean (hh i j)

#print axioms weakProductL2Directional_family_of_bounded_strong_approximation
#print axioms weakProductL2_second_jets_of_bounded_strong_approximation
end TheoremT.Continuum
