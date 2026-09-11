import CompactWeightedCutoffDirectionalEnergy_v1
import PartialSpectatorDirectional_v1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem euclidean_product_volume_isAddHaar :
    ((volume : Measure (EuclideanSpace ℝ ι)).prod
      (volume : Measure (EuclideanSpace ℝ κ))).IsAddHaarMeasure := by
  exact { toIsFiniteMeasureOnCompacts := inferInstance
          toIsAddLeftInvariant := inferInstance
          toIsOpenPosMeasure := inferInstance }

theorem compact_spectator_coordinate_cutoff_energy
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    {u : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → F}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hu : ContDiff ℝ ∞ u)
    (i : ι) (v : EuclideanSpace ℝ κ) :
    (∫ p, (p.1 i)^2*‖partialTDirectional (fun q => η q • u q) v p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) =
      -(∫ p, (p.1 i)^2*inner ℝ ((η p)^2 • u p)
        (partialTDirectional (partialTDirectional u v) v p)
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) +
      (∫ p, (p.1 i)^2*‖(partialTDirectional η v p) • u p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) := by
  letI := euclidean_product_volume_isAddHaar (ι := ι) (κ := κ)
  let L : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
  have hw : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => p.1 i) := L.contDiff
  have hw0 (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
      fderiv ℝ (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => q.1 i) p (0,v) = 0 := by
    change fderiv ℝ L p (0,v) = 0
    rw [L.fderiv]
    simp [L]
  exact compact_weighted_cutoff_directional_energy (μ := (volume : Measure (EuclideanSpace ℝ ι)).prod volume)
    hw hη hc hu (0,v) hw0

theorem compact_fst_norm_sq_mul_integral
    {f : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ p, ‖p.1‖^2*f p ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) =
      ∑ i : ι,∫ p, (p.1 i)^2*f p ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume) := by
  have hI (i : ι) : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ => (p.1 i)^2*f p)
      ((volume : Measure (EuclideanSpace ℝ ι)).prod volume) :=
    ((((EuclideanSpace.proj i).continuous.comp continuous_fst).pow 2).mul hf).integrable_of_hasCompactSupport hc.mul_left
  simp_rw [EuclideanSpace.real_norm_sq_eq,Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => hI i)

theorem compact_spectator_norm_sq_cutoff_energy
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    {u : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → F}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hu : ContDiff ℝ ∞ u)
    (v : EuclideanSpace ℝ κ) :
    (∫ p, ‖p.1‖^2*‖partialTDirectional (fun q => η q • u q) v p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) =
      -(∫ p, ‖p.1‖^2*inner ℝ ((η p)^2 • u p)
        (partialTDirectional (partialTDirectional u v) v p)
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) +
      (∫ p, ‖p.1‖^2*‖(partialTDirectional η v p) • u p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) := by
  have hηu : ContDiff ℝ ∞ (fun p => η p • u p) := hη.smul hu
  have hcu : HasCompactSupport (fun p => η p • u p) := by
    apply hc.mono
    intro p hp
    change η p ≠ 0
    intro hz
    exact hp (by simp [hz])
  have hA : Continuous (fun p => ‖partialTDirectional (fun q => η q • u q) v p‖^2) :=
    (partialTDirectional_contDiff hηu v).continuous.norm.pow 2
  have hcA : HasCompactSupport (fun p => ‖partialTDirectional (fun q => η q • u q) v p‖^2) := by
    apply (partialTDirectional_hasCompactSupport hcu v).mono
    intro p hp
    change partialTDirectional (fun q => η q • u q) v p ≠ 0
    intro hz
    exact hp (by simp [hz])
  have hB : Continuous (fun p => inner ℝ ((η p)^2 • u p)
      (partialTDirectional (partialTDirectional u v) v p)) := by
    simpa only [Pi.smul_def'] using ((hη.pow 2).smul hu).continuous.inner (𝕜 := ℝ)
      (partialTDirectional_contDiff (partialTDirectional_contDiff hu v) v).continuous
  have hcB : HasCompactSupport (fun p => inner ℝ ((η p)^2 • u p)
      (partialTDirectional (partialTDirectional u v) v p)) := by
    apply hc.mono
    intro p hp
    change η p ≠ 0
    intro hz
    exact hp (by simp [hz])
  have hC : Continuous (fun p => ‖(partialTDirectional η v p) • u p‖^2) := by
    have hcuC : Continuous (fun p => (partialTDirectional η v p) • u p) :=
      (partialTDirectional_contDiff hη v).continuous.smul hu.continuous
    exact hcuC.norm.pow 2
  have hcC : HasCompactSupport (fun p => ‖(partialTDirectional η v p) • u p‖^2) := by
    apply (partialTDirectional_hasCompactSupport hc v).mono
    intro p hp
    change partialTDirectional η v p ≠ 0
    intro hz
    exact hp (by simp [hz])
  rw [compact_fst_norm_sq_mul_integral hA hcA,
    compact_fst_norm_sq_mul_integral hB hcB,compact_fst_norm_sq_mul_integral hC hcC]
  simp_rw [compact_spectator_coordinate_cutoff_energy hη hc hu,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]

#print axioms euclidean_product_volume_isAddHaar
#print axioms compact_spectator_coordinate_cutoff_energy
#print axioms compact_fst_norm_sq_mul_integral
#print axioms compact_spectator_norm_sq_cutoff_energy
end TheoremT.Continuum
