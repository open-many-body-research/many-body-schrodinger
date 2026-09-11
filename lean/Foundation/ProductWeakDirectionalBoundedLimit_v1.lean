import TemperedL2BoundedLimit_v1
import ProductDistributionDirectionalConverse_v2

/-!
Strong L2 approximation with uniformly bounded genuine weak derivatives on
the ordinary product gives a genuine weak derivative of the limit with the
same norm bound. Exact Euclidean-copy isometries preserve the constant.
The hypothesis supplies no derivative or weak-limit identity at the limit.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2Directional_of_bounded_strong_approximation
    (u d : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (v : Y × T)
    (hf : Tendsto u atTop (𝓝 f))
    (hd : ∀ n, WeakProductL2Directional (u n) (d n) v)
    {C : ℝ} (hb : ∀ n, ‖d n‖ ≤ C) :
    ∃ g : Lp ℂ 2 (volume : Measure (Y × T)),
      ‖g‖ ≤ C ∧ WeakProductL2Directional f g v := by
  have hlf : Tendsto (fun n => productEuclideanLift (u n)) atTop
      (𝓝 (productEuclideanLift f)) :=
    (productEuclideanLift.continuous.tendsto f).comp hf
  have hld (n : ℕ) : WeakL2Directional (productEuclideanLift (u n))
      (productEuclideanLift (d n)) (WithLp.toLp 2 v) :=
    weakL2Directional_productEuclideanLift (hd n)
  have hlb (n : ℕ) : ‖productEuclideanLift (d n)‖ ≤ C := by
    simpa only [LinearIsometry.norm_map] using hb n
  obtain ⟨g,hg,hgD⟩ := weakL2Directional_of_bounded_strong_approximation
    (fun n => productEuclideanLift (u n)) (fun n => productEuclideanLift (d n))
    (productEuclideanLift f) (WithLp.toLp 2 v) hlf hld hlb
  refine ⟨productEuclideanUnlift g, ?_, ?_⟩
  · simpa only [LinearIsometry.norm_map] using hg
  · have h := weakProductL2Directional_of_euclidean hgD
    simpa only [productEuclideanUnlift_lift] using h

#print axioms weakProductL2Directional_of_bounded_strong_approximation
end TheoremT.Continuum
