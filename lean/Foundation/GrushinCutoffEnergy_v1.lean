import CompactSpectatorCutoffEnergy_v1
import EuclideanGrushinPrincipal_v1

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def grushinGradientEnergy (c : ℝ)
    (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ) : ℝ :=
  (∑ i : ι, ∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2
    ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) +
  c*(∑ j : κ, ∫ p, ‖p.1‖^2*‖partialTDirectional G (oscillatorBasis j) p‖^2
    ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume))

def grushinCutoffEnergy (c : ℝ)
    (η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ)
    (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ) : ℝ :=
  (∑ i : ι, ∫ p, ‖(partialYDirectional η (oscillatorBasis i) p) • G p‖^2
    ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) +
  c*(∑ j : κ, ∫ p, ‖p.1‖^2*‖(partialTDirectional η (oscillatorBasis j) p) • G p‖^2
    ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume))

theorem compact_cutoff_grushin_energy (c : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hG : ContDiff ℝ ∞ G) :
    grushinGradientEnergy c (fun p => η p • G p) =
      (∫ p, inner ℝ ((η p)^2 • G p) (euclideanGrushin c G p)
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) +
      grushinCutoffEnergy c η G := by
  let μ : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :=
    (volume : Measure (EuclideanSpace ℝ ι)).prod volume
  letI : μ.IsAddHaarMeasure := euclidean_product_volume_isAddHaar
  have hW : ContDiff ℝ ∞ (fun p => (η p)^2 • G p) := (hη.pow 2).smul hG
  have hcW : HasCompactSupport (fun p => (η p)^2 • G p) := by
    apply hc.mono
    intro p hp
    change η p ≠ 0
    intro hz
    exact hp (by simp [hz])
  have iY (i : ι) : Integrable (fun p => inner ℝ ((η p)^2 • G p)
      (partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis i) p)) μ :=
    compact_real_inner_integrable_general hW.continuous
      (partialYDirectional_contDiff (partialYDirectional_contDiff hG _) _).continuous hcW
  have iT (j : κ) : Integrable (fun p => ‖p.1‖^2*inner ℝ ((η p)^2 • G p)
      (partialTDirectional (partialTDirectional G (oscillatorBasis j)) (oscillatorBasis j) p)) μ := by
    have h := compact_real_inner_integrable_general (μ := μ) hW.continuous
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).smul
        (partialTDirectional_contDiff (partialTDirectional_contDiff hG (oscillatorBasis j)) (oscillatorBasis j))).continuous) hcW
    simpa only [Pi.smul_def',Function.comp_apply,real_inner_smul_right] using h
  have hys := integrable_finsetSum Finset.univ (fun i _ => iY i)
  have hts := integrable_finsetSum Finset.univ (fun j _ => iT j)
  have hneg : Integrable (fun p => -(∑ i : ι,inner ℝ ((η p)^2 • G p)
      (partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis i) p))) μ := hys.neg
  have hp (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
      inner ℝ ((η p)^2 • G p) (euclideanGrushin c G p) =
        -(∑ i : ι,inner ℝ ((η p)^2 • G p)
          (partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis i) p)) -
        c*(∑ j : κ,‖p.1‖^2*inner ℝ ((η p)^2 • G p)
          (partialTDirectional (partialTDirectional G (oscillatorBasis j)) (oscillatorBasis j) p)) := by
    simp only [euclideanGrushin,grushinYLaplacian,grushinTLaplacian,inner_sub_right,
      inner_neg_right,inner_sum,real_inner_smul_right,Finset.mul_sum,mul_assoc]
  have hi : (∫ p,inner ℝ ((η p)^2 • G p) (euclideanGrushin c G p) ∂μ) =
      -(∑ i : ι,∫ p,inner ℝ ((η p)^2 • G p)
        (partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis i) p) ∂μ) -
      c*(∑ j : κ,∫ p,‖p.1‖^2*inner ℝ ((η p)^2 • G p)
        (partialTDirectional (partialTDirectional G (oscillatorBasis j)) (oscillatorBasis j) p) ∂μ) := by
    simp_rw [hp]
    rw [integral_sub hneg (hts.const_mul c),integral_neg,integral_const_mul,
      integral_finsetSum _ (fun i _ => iY i),integral_finsetSum _ (fun j _ => iT j)]
  have hy (i : ι) := compact_cutoff_directional_energy (μ := μ) hη hc hG (oscillatorBasis i,0)
  change ∀ i : ι,
    (∫ p,‖partialYDirectional (fun q => η q • G q) (oscillatorBasis i) p‖^2 ∂μ) =
      -(∫ p,inner ℝ ((η p)^2 • G p)
        (partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis i) p) ∂μ) +
      (∫ p,‖(partialYDirectional η (oscillatorBasis i) p) • G p‖^2 ∂μ) at hy
  dsimp only [μ] at hy hi
  unfold grushinGradientEnergy grushinCutoffEnergy
  change _ = (∫ p,inner ℝ ((η p)^2 • G p) (euclideanGrushin c G p) ∂μ) + _
  rw [hi]
  simp only [hy, compact_spectator_norm_sq_cutoff_energy hη hc hG,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

#print axioms compact_cutoff_grushin_energy
end TheoremT.Continuum
