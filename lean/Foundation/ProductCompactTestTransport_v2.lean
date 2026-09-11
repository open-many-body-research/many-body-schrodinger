import ProductDistributionLaplacian_v1
import ProductWeakDirectionalLift_v1
import GenericCompactLaplacianTests_v1

/-!
Version 2 reuses the canonical L2 lift pairing from ProductWeakDirectionalLift_v1.
Actual compact test functions and their factor-coordinate Laplacian transported
between the ordinary product and its Euclidean `WithLp 2` copy. The product
retains its existing maximum norm and its actual product Lebesgue measure.
-/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian ContDiff BigOperators
namespace TheoremT.Continuum

variable {Y T ι κ : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
  [Fintype ι] [Fintype κ]

def productFactorLaplacian (bY : OrthonormalBasis ι ℝ Y)
    (bT : OrthonormalBasis κ ℝ T) (φ : Y × T → ℝ) (p : Y × T) : ℝ :=
  (∑ k : ι, fderiv ℝ (fun q => fderiv ℝ φ q (bY k, (0 : T))) p (bY k, (0 : T))) +
  (∑ l : κ, fderiv ℝ (fun q => fderiv ℝ φ q ((0 : Y), bT l)) p ((0 : Y), bT l))

theorem product_second_directional_euclidean_pullback
    {ψ : WithLp 2 (Y × T) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (p v q : Y × T) :
    fderiv ℝ (fun r => fderiv ℝ (ψ ∘ WithLp.toLp 2) r v) p q =
      fderiv ℝ (fun r => fderiv ℝ ψ r (WithLp.toLp 2 v))
        (WithLp.toLp 2 p) (WithLp.toLp 2 q) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).symm
  have hf (r : Y × T) :
      fderiv ℝ (ψ ∘ e) r v = fderiv ℝ ψ (e r) (e v) := by
    rw [(((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp r
      e.hasFDerivAt).fderiv]
    rfl
  have he : (fun r => fderiv ℝ (ψ ∘ e) r v) =
      (fun r => fderiv ℝ ψ r (e v)) ∘ e := funext hf
  change fderiv ℝ (fun r => fderiv ℝ (ψ ∘ e) r v) p q = _
  rw [he]
  have hd : ContDiff ℝ ∞ (fun r => fderiv ℝ ψ r (e v)) :=
    (hψ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  rw [(((hd.differentiable (by simp)).differentiableAt.hasFDerivAt).comp p
    e.hasFDerivAt).fderiv]
  rfl

theorem product_factor_laplacian_euclidean_pullback
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {ψ : WithLp 2 (Y × T) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (p : Y × T) :
    productFactorLaplacian bY bT (ψ ∘ WithLp.toLp 2) p = Δ ψ (WithLp.toLp 2 p) := by
  rw [generic_compact_laplacian_directional_sum hψ hc (bY.prod bT),
    Fintype.sum_sum_type]
  simp only [productFactorLaplacian, product_second_directional_euclidean_pullback hψ,
    OrthonormalBasis.prod_apply, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply]

#print axioms product_second_directional_euclidean_pullback
#print axioms product_factor_laplacian_euclidean_pullback
end TheoremT.Continuum
