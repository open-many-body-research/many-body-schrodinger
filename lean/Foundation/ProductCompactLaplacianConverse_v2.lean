import GenericDistributionLaplacianConverse_v1
import ProductCompactTestTransport_v2

/-!
Version 2 composes with ProductWeakDirectionalLift_v1 and the compact H2 density
branch through ProductCompactTestTransport_v2.
The factor-coordinate Laplacian identity against every actual smooth compact
real test on the ordinary product implies the actual tempered-distribution
equation on its Euclidean copy and all ordered weak L2 derivatives through
order two on the original product. No derivative-existence or density premise
is present. The existence of L2 derivative witnesses is not an algorithm.
-/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff BigOperators
namespace TheoremT.Continuum

variable {Y T ι κ : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
  [Fintype ι] [Fintype κ]

theorem product_distribution_laplacian_of_compact_factor_tests
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    (f w : Lp ℂ 2 (volume : Measure (Y × T)))
    (h : ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, φ p • w p) = ∫ p, productFactorLaplacian bY bT φ p • f p) :
    Δ (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)) =
      (productEuclideanLift w : 𝓢'(WithLp 2 (Y × T), ℂ)) := by
  apply generic_distribution_laplacian_of_compact_real_tests
  intro ψ hψ hc
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).symm
  have hφ : ContDiff ℝ ∞ (ψ ∘ WithLp.toLp 2) := hψ.comp e.contDiff
  have hcφ : HasCompactSupport (ψ ∘ WithLp.toLp 2) :=
    hc.comp_homeomorph e.toHomeomorph
  rw [productEuclideanLift_test, productEuclideanLift_test]
  calc
    (∫ p, ψ (WithLp.toLp 2 p) • w p) =
        ∫ p, productFactorLaplacian bY bT (ψ ∘ WithLp.toLp 2) p • f p :=
      h (ψ ∘ WithLp.toLp 2) hφ hcφ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [product_factor_laplacian_euclidean_pullback bY bT hψ hc]

theorem product_factor_distribution_laplacian_of_compact_tests
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    (f w : Lp ℂ 2 (volume : Measure (Y × T)))
    (h : ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, φ p • w p) = ∫ p, productFactorLaplacian bY bT φ p • f p) :
    (∑ k : ι, ∂_{WithLp.toLp 2 (bY k, (0 : T))}
      (∂_{WithLp.toLp 2 (bY k, (0 : T))}
        (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)))) +
    (∑ l : κ, ∂_{WithLp.toLp 2 ((0 : Y), bT l)}
      (∂_{WithLp.toLp 2 ((0 : Y), bT l)}
        (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)))) =
      (productEuclideanLift w : 𝓢'(WithLp 2 (Y × T), ℂ)) := by
  rw [← distribution_laplacian_product_basis bY bT]
  exact product_distribution_laplacian_of_compact_factor_tests bY bT f w h

theorem product_weak_second_jets_of_compact_factor_laplacian_tests
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    (f w : Lp ℂ 2 (volume : Measure (Y × T)))
    (h : ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, φ p • w p) = ∫ p, productFactorLaplacian bY bT φ p • f p) :
    ∃ d : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ v, WeakProductL2Directional f (d v) v) ∧
      ∀ v q : Y × T, ∃ e : Lp ℂ 2 (volume : Measure (Y × T)),
        WeakProductL2Directional (d v) e q :=
  product_exists_weak_first_and_second_jets_of_euclidean_laplacian f w
    (product_distribution_laplacian_of_compact_factor_tests bY bT f w h)

#print axioms product_distribution_laplacian_of_compact_factor_tests
#print axioms product_factor_distribution_laplacian_of_compact_tests
#print axioms product_weak_second_jets_of_compact_factor_laplacian_tests
end TheoremT.Continuum
