import WeakDomainAlgebra_v2

/-! Actual coordinate-permutation covariance of distributional Sobolev derivatives. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum

theorem pullback_ae {N : ℕ} (π : Equiv.Perm (Fin N)) (f : SpatialL2 N) :
    (pullback π f : Configuration N → ℂ) =ᵐ[volume] f ∘ permuteSpace π := by
  exact Lp.coeFn_compMeasurePreserving f (permuteSpace π).measurePreserving

theorem permuteSpace_symm_coordinateVector {N : ℕ} (π : Equiv.Perm (Fin N))
    (k : Coordinate N) :
    (permuteSpace π).symm (coordinateVector k) =
      coordinateVector (coordinatePermutation π k) := by
  simp only [permuteSpace, coordinateVector,
    LinearIsometryEquiv.piLpCongrLeft_symm, Equiv.symm_symm,
    LinearIsometryEquiv.piLpCongrLeft_single]

theorem integral_test_pullback {N : ℕ} (π : Equiv.Perm (Fin N)) (f : SpatialL2 N)
    (φ : Configuration N → ℝ) :
    (∫ x, φ x • (pullback π f) x) =
      ∫ y, φ ((permuteSpace π).symm y) • f y := by
  calc
    _ = ∫ x, φ x • f (permuteSpace π x) := by
      apply integral_congr_ae
      filter_upwards [pullback_ae π f] with x hx
      rw [hx]
      rfl
    _ = _ := by
      have he := (permuteSpace π).measurePreserving.integral_comp
        (permuteSpace π).toHomeomorph.measurableEmbedding
        (fun y => φ ((permuteSpace π).symm y) • f y)
      simpa only [LinearIsometryEquiv.symm_apply_apply] using he

/-- The transformed coordinate is π(k), matching x_i ↦ x_(π i). -/
theorem weakPartial_pullback {N : ℕ} (π : Equiv.Perm (Fin N))
    {f g : SpatialL2 N} {k : Coordinate N} (hg : WeakPartial f g k) :
    WeakPartial (pullback π f) (pullback π g) (coordinatePermutation π k) := by
  intro φ hφ hc
  let e := permuteSpace π
  have htest : ContDiff ℝ ∞ (φ ∘ e.symm) :=
    hφ.comp e.symm.toContinuousLinearEquiv.contDiff
  have hsupport : HasCompactSupport (φ ∘ e.symm) :=
    hc.comp_homeomorph e.symm.toHomeomorph
  have hchain (y : Configuration N) :
      fderiv ℝ (φ ∘ e.symm) y (coordinateVector k) =
        fderiv ℝ φ (e.symm y) (coordinateVector (coordinatePermutation π k)) := by
    have heD : HasFDerivAt (e.symm : Configuration N → Configuration N)
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap y :=
      e.symm.toContinuousLinearEquiv.hasFDerivAt
    have hcomp := (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y heD
    rw [hcomp.fderiv]
    change fderiv ℝ φ (e.symm y) (e.symm (coordinateVector k)) = _
    rw [show e.symm (coordinateVector k) =
      coordinateVector (coordinatePermutation π k) from permuteSpace_symm_coordinateVector π k]
  rw [integral_test_pullback, integral_test_pullback]
  have h := hg (φ ∘ e.symm) htest hsupport
  simpa only [Function.comp_apply, hchain] using h

/-- The actual weak H1 space is preserved, using permuted derivative witnesses. -/
theorem HasH1.permute {N : ℕ} (π : Equiv.Perm (Fin N))
    {f : SpatialL2 N} (hf : HasH1 f) : HasH1 (pullback π f) := by
  obtain ⟨d, hd⟩ := hf
  refine ⟨fun k => pullback π (d ((coordinatePermutation π).symm k)), ?_⟩
  intro k
  simpa only [Equiv.apply_symm_apply] using
    weakPartial_pullback π (hd ((coordinatePermutation π).symm k))

/-- All mixed weak second derivatives transform; no smoothness premise is substituted. -/
theorem HasH2.permute {N : ℕ} (π : Equiv.Perm (Fin N))
    {f : SpatialL2 N} (hf : HasH2 f) : HasH2 (pullback π f) := by
  obtain ⟨d, hd, he⟩ := hf
  refine ⟨fun k => pullback π (d ((coordinatePermutation π).symm k)), ?_, ?_⟩
  · intro k
    simpa only [Equiv.apply_symm_apply] using
      weakPartial_pullback π (hd ((coordinatePermutation π).symm k))
  · intro k l
    obtain ⟨v, hv⟩ := he ((coordinatePermutation π).symm k)
      ((coordinatePermutation π).symm l)
    refine ⟨pullback π v, ?_⟩
    simpa only [Equiv.apply_symm_apply] using weakPartial_pullback π hv

#print axioms integral_test_pullback
#print axioms weakPartial_pullback
#print axioms HasH1.permute
#print axioms HasH2.permute
end TheoremT.Continuum
