import WeakGrushinAnisotropicLimitCore_v1
import ProductWeakJetsBoundedLimit_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2_anisotropic_jets_of_bounded_strong_approximation
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → Y) (w : κ → T)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (dy : ℕ → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (dt : ℕ → κ → Lp ℂ 2 (volume : Measure (Y × T)))
    (eyy : ℕ → ι → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (hf : Tendsto u atTop (𝓝 f))
    (hdy : ∀ n i, WeakProductL2Directional (u n) (dy n i) (v i,0))
    (hdt : ∀ n j, WeakProductL2Directional (u n) (dt n j) (0,w j))
    (heyy : ∀ n i j, WeakProductL2Directional (dy n i) (eyy n i j) (v j,0))
    {C : ℝ} (hb : ∀ n, (∑ i, ‖dy n i‖^2) + (∑ j, ‖dt n j‖^2) +
      (∑ i, ∑ j, ‖eyy n i j‖^2) ≤ C) :
    ∃ gy : ι → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ hyy : ι → ι → Lp ℂ 2 (volume : Measure (Y × T)),
      ((∑ i, ‖gy i‖^2) + (∑ j, ‖gt j‖^2) + (∑ i, ∑ j, ‖hyy i j‖^2) ≤ C) ∧
      (∀ i, WeakProductL2Directional f (gy i) (v i,0)) ∧
      (∀ j, WeakProductL2Directional f (gt j) (0,w j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (v j,0) := by
  have hlf : Tendsto (fun n => productEuclideanLift (u n)) atTop (𝓝 (productEuclideanLift f)) :=
    (productEuclideanLift.continuous.tendsto f).comp hf
  have hlb (n : ℕ) : (∑ i, ‖productEuclideanLift (dy n i)‖^2) +
      (∑ j, ‖productEuclideanLift (dt n j)‖^2) +
      (∑ i, ∑ j, ‖productEuclideanLift (eyy n i j)‖^2) ≤ C := by
    simpa only [LinearIsometry.norm_map] using hb n
  obtain ⟨gy,gt,hyy,hb',hgy,hgt,hhyy⟩ := weakL2_anisotropic_jets_of_bounded_strong_approximation
    (fun i => WithLp.toLp 2 (v i, (0 : T))) (fun j => WithLp.toLp 2 ((0 : Y),w j))
    (fun n => productEuclideanLift (u n)) (fun n i => productEuclideanLift (dy n i))
    (fun n j => productEuclideanLift (dt n j)) (fun n i j => productEuclideanLift (eyy n i j))
    (productEuclideanLift f) hlf
    (fun n i => weakL2Directional_productEuclideanLift (hdy n i))
    (fun n j => weakL2Directional_productEuclideanLift (hdt n j))
    (fun n i j => weakL2Directional_productEuclideanLift (heyy n i j)) hlb
  refine ⟨(fun i => productEuclideanUnlift (gy i)), (fun j => productEuclideanUnlift (gt j)),
    (fun i j => productEuclideanUnlift (hyy i j)), ?_, ?_, ?_, ?_⟩
  · simpa only [LinearIsometry.norm_map] using hb'
  · intro i
    simpa only [productEuclideanUnlift_lift] using weakProductL2Directional_of_euclidean (hgy i)
  · intro j
    simpa only [productEuclideanUnlift_lift] using weakProductL2Directional_of_euclidean (hgt j)
  · intro i j
    exact weakProductL2Directional_of_euclidean (hhyy i j)

#print axioms weakProductL2_anisotropic_jets_of_bounded_strong_approximation
end TheoremT.Continuum
