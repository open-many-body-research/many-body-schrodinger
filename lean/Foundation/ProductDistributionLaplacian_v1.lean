import ProductWeakEllipticGain_v1
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Exact decomposition of the Euclidean-copy distributional Laplacian into its
actual factor-coordinate derivatives. This makes the premise of the product
weak-H2 theorem explicit; neither a metric change nor a Jacobian is hidden.
-/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv BigOperators
namespace TheoremT.Continuum

variable {Y T ι κ : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
  [Fintype ι] [Fintype κ]

theorem distribution_laplacian_product_basis
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    (u : 𝓢'(WithLp 2 (Y × T), ℂ)) :
    Δ u =
      (∑ k : ι, ∂_{WithLp.toLp 2 (bY k, (0 : T))}
        (∂_{WithLp.toLp 2 (bY k, (0 : T))} u)) +
      (∑ l : κ, ∂_{WithLp.toLp 2 ((0 : Y), bT l)}
        (∂_{WithLp.toLp 2 ((0 : Y), bT l)} u)) := by
  rw [laplacian_eq_sum (bY.prod bT), Fintype.sum_sum_type]
  simp only [OrthonormalBasis.prod_apply, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply]

theorem product_weak_second_jets_of_factor_distribution_laplacian
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    (f w : Lp ℂ 2 (volume : Measure (Y × T)))
    (hw :
      (∑ k : ι, ∂_{WithLp.toLp 2 (bY k, (0 : T))}
        (∂_{WithLp.toLp 2 (bY k, (0 : T))}
          (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)))) +
      (∑ l : κ, ∂_{WithLp.toLp 2 ((0 : Y), bT l)}
        (∂_{WithLp.toLp 2 ((0 : Y), bT l)}
          (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)))) =
        (productEuclideanLift w : 𝓢'(WithLp 2 (Y × T), ℂ))) :
    ∃ d : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ v, WeakProductL2Directional f (d v) v) ∧
      ∀ v q : Y × T, ∃ e : Lp ℂ 2 (volume : Measure (Y × T)),
        WeakProductL2Directional (d v) e q := by
  apply product_exists_weak_first_and_second_jets_of_euclidean_laplacian f w
  rwa [distribution_laplacian_product_basis bY bT]

#print axioms distribution_laplacian_product_basis
#print axioms product_weak_second_jets_of_factor_distribution_laplacian
end TheoremT.Continuum
