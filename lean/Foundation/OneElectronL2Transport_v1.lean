import OneElectronEuclidean_v1

/-! Actual unitary L2 transport and preservation of the punctured smooth core
under the one-electron Euclidean coordinate isometry. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
open TheoremT.HydrogenPolynomial

abbrev EuclideanOneL2 := Lp ℂ 2 (volume : Measure AngularR3)

def oneElectronL2ToEuclidean : SpatialL2 1 →ₗᵢ[ℂ] EuclideanOneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ oneElectronEuclidean.symm
    oneElectronEuclidean.symm.measurePreserving

def oneElectronL2FromEuclidean : EuclideanOneL2 →ₗᵢ[ℂ] SpatialL2 1 :=
  Lp.compMeasurePreservingₗᵢ ℂ oneElectronEuclidean oneElectronEuclidean.measurePreserving

theorem oneElectronL2ToEuclidean_ae (f : SpatialL2 1) :
    oneElectronL2ToEuclidean f =ᵐ[volume] f ∘ oneElectronEuclidean.symm :=
  Lp.coeFn_compMeasurePreserving f oneElectronEuclidean.symm.measurePreserving

theorem oneElectronL2FromEuclidean_ae (f : EuclideanOneL2) :
    oneElectronL2FromEuclidean f =ᵐ[volume] f ∘ oneElectronEuclidean :=
  Lp.coeFn_compMeasurePreserving f oneElectronEuclidean.measurePreserving

theorem oneElectronL2ToEuclidean_from (f : EuclideanOneL2) :
    oneElectronL2ToEuclidean (oneElectronL2FromEuclidean f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (oneElectronEuclidean ∘ oneElectronEuclidean.symm) = id :=
    funext oneElectronEuclidean.apply_symm_apply
  simp only [he, Lp.compMeasurePreserving_id_apply]

theorem oneElectronL2FromEuclidean_to (f : SpatialL2 1) :
    oneElectronL2FromEuclidean (oneElectronL2ToEuclidean f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (oneElectronEuclidean.symm ∘ oneElectronEuclidean) = id :=
    funext oneElectronEuclidean.symm_apply_apply
  simp only [he, Lp.compMeasurePreserving_id_apply]

def oneElectronL2EuclideanEquiv : SpatialL2 1 ≃ₗᵢ[ℂ] EuclideanOneL2 :=
  { oneElectronL2ToEuclidean with
    invFun := oneElectronL2FromEuclidean
    left_inv := oneElectronL2FromEuclidean_to
    right_inv := oneElectronL2ToEuclidean_from }

theorem oneElectronL2ToEuclidean_representative {f : SpatialL2 1}
    {u : Configuration 1 → ℂ} (hu : f =ᵐ[volume] u) :
    oneElectronL2ToEuclidean f =ᵐ[volume]
      fun x => u (oneElectronEuclidean.symm x) := by
  filter_upwards [oneElectronL2ToEuclidean_ae f,
    oneElectronEuclidean.symm.measurePreserving.quasiMeasurePreserving.ae hu] with x hx hu
  exact hx.trans hu

theorem oneElectronEuclidean_contDiff {u : Configuration 1 → ℂ}
    (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x => u (oneElectronEuclidean.symm x)) :=
  hu.comp oneElectronEuclidean.symm.toContinuousLinearEquiv.contDiff

theorem oneElectronEuclidean_compact {u : Configuration 1 → ℂ}
    (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => u (oneElectronEuclidean.symm x)) :=
  hu.comp_isClosedEmbedding oneElectronEuclidean.symm.toHomeomorph.isClosedEmbedding

theorem oneElectronEuclidean_punctured {u : Configuration 1 → ℂ}
    (hu : (0 : Configuration 1) ∉ tsupport u) :
    (0 : AngularR3) ∉ tsupport (fun x => u (oneElectronEuclidean.symm x)) := by
  intro hz
  have h := tsupport_comp_subset_preimage u oneElectronEuclidean.symm.continuous hz
  apply hu
  simpa only [Set.mem_preimage, map_zero] using h

#print axioms oneElectronL2EuclideanEquiv
#print axioms oneElectronL2ToEuclidean_representative
#print axioms oneElectronEuclidean_punctured
end TheoremT.Continuum
