import GenericWeakEllipticGain_v1
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
The global Euclidean elliptic estimate transported to the ordinary Cartesian
product (whose norm is the maximum norm). The coordinate change is the identity
on points through `WithLp 2`; Mathlib proves exact preservation of product
Lebesgue measure. The Laplacian premise is explicitly on that Euclidean copy.
The output uses actual product-space compact tests and ordered weak derivatives.
-/

noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff

namespace TheoremT.Continuum

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

def productEuclideanLift : Lp ℂ 2 (volume : Measure (Y × T)) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (WithLp 2 (Y × T))) :=
  Lp.compMeasurePreservingₗᵢ ℂ WithLp.ofLp (WithLp.volume_preserving_ofLp Y T)

def productEuclideanUnlift : Lp ℂ 2 (volume : Measure (WithLp 2 (Y × T))) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (Y × T)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (WithLp.toLp 2) (WithLp.volume_preserving_toLp Y T)

theorem productEuclideanLift_ae (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    productEuclideanLift f =ᵐ[volume] f ∘ WithLp.ofLp :=
  Lp.coeFn_compMeasurePreserving f (WithLp.volume_preserving_ofLp Y T)

theorem productEuclideanUnlift_ae (f : Lp ℂ 2 (volume : Measure (WithLp 2 (Y × T)))) :
    productEuclideanUnlift f =ᵐ[volume] f ∘ WithLp.toLp 2 :=
  Lp.coeFn_compMeasurePreserving f (WithLp.volume_preserving_toLp Y T)

theorem productEuclideanUnlift_lift (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    productEuclideanUnlift (productEuclideanLift f) = f := by
  apply Lp.ext
  filter_upwards [productEuclideanUnlift_ae (productEuclideanLift f),
    (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae (productEuclideanLift_ae f)]
    with p hp hq
  simpa only [Function.comp_apply, WithLp.ofLp_toLp] using hp.trans hq

def WeakProductL2Directional (f g : Lp ℂ 2 (volume : Measure (Y × T)))
    (v : Y × T) : Prop :=
  ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ p, φ p • g p) = -(∫ p, fderiv ℝ φ p v • f p)

theorem productEuclideanUnlift_test
    (f : Lp ℂ 2 (volume : Measure (WithLp 2 (Y × T)))) (φ : Y × T → ℝ) :
    (∫ p, φ p • productEuclideanUnlift f p) = ∫ q, φ q.ofLp • f q := by
  calc
    _ = ∫ p, φ p • f (WithLp.toLp 2 p) := by
      apply integral_congr_ae
      filter_upwards [productEuclideanUnlift_ae f] with p hp
      rw [hp]
      rfl
    _ = _ := by
      have hh := (WithLp.volume_preserving_toLp Y T).integral_comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).symm.toHomeomorph.measurableEmbedding
        (fun q : WithLp 2 (Y × T) => φ q.ofLp • f q)
      simpa only [WithLp.ofLp_toLp] using hh

theorem weakProductL2Directional_of_euclidean
    {f g : Lp ℂ 2 (volume : Measure (WithLp 2 (Y × T)))} {v : Y × T}
    (h : WeakL2Directional f g (WithLp.toLp 2 v)) :
    WeakProductL2Directional (productEuclideanUnlift f) (productEuclideanUnlift g) v := by
  intro φ hφ hc
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ Y T
  have htest : ContDiff ℝ ∞ (φ ∘ e) := hφ.comp e.contDiff
  have hsupport : HasCompactSupport (φ ∘ e) := hc.comp_homeomorph e.toHomeomorph
  have hchain (q : WithLp 2 (Y × T)) :
      fderiv ℝ (φ ∘ e) q (WithLp.toLp 2 v) = fderiv ℝ φ q.ofLp v := by
    have hh := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp q e.hasFDerivAt
    rw [hh.fderiv]
    rfl
  rw [productEuclideanUnlift_test, productEuclideanUnlift_test]
  have hh := h (φ ∘ e) htest hsupport
  have heq (q : WithLp 2 (Y × T)) : e q = q.ofLp := rfl
  simpa only [Function.comp_apply, hchain, heq] using hh

theorem product_exists_weak_first_and_second_jets_of_euclidean_laplacian
    (f w : Lp ℂ 2 (volume : Measure (Y × T)))
    (hw : Δ (productEuclideanLift f : 𝓢'(WithLp 2 (Y × T), ℂ)) =
      (productEuclideanLift w : 𝓢'(WithLp 2 (Y × T), ℂ))) :
    ∃ d : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ v, WeakProductL2Directional f (d v) v) ∧
      ∀ v q : Y × T, ∃ e : Lp ℂ 2 (volume : Measure (Y × T)),
        WeakProductL2Directional (d v) e q := by
  obtain ⟨d, hd, hdd⟩ := exists_weakL2_first_and_second_jets_of_distribution_laplacian
    (productEuclideanLift f) (productEuclideanLift w) hw
  refine ⟨fun v => productEuclideanUnlift (d (WithLp.toLp 2 v)), ?_, ?_⟩
  · intro v
    have hh := weakProductL2Directional_of_euclidean (hd (WithLp.toLp 2 v))
    rwa [productEuclideanUnlift_lift] at hh
  · intro v q
    obtain ⟨e, he⟩ := hdd (WithLp.toLp 2 v) (WithLp.toLp 2 q)
    exact ⟨productEuclideanUnlift e, weakProductL2Directional_of_euclidean he⟩

#print axioms productEuclideanUnlift_lift
#print axioms weakProductL2Directional_of_euclidean
#print axioms product_exists_weak_first_and_second_jets_of_euclidean_laplacian

end TheoremT.Continuum
