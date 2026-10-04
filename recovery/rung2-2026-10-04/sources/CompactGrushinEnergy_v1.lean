import GrushinCutoffEnergy_v1
import FiniteDimSmoothCutoff_v1

/-! Actual compact smooth Grushin energy, obtained by a proved plateau
cutoff around the support. No energy identity is assumed. Product Lebesgue
measure and the principal operator are unchanged. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff RealInnerProductSpace BigOperators Topology
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem compact_grushin_energy (c : ℝ)
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G) :
    grushinGradientEnergy c G =
      ∫ p, inner ℝ (G p) (euclideanGrushin c G p)
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume) := by
  obtain ⟨η,hη,hcη,_hs,h1⟩ := finiteDim_compact_exists_smooth_cutoff
    hcG.isCompact isOpen_univ (Set.subset_univ _)
  have hcut : (fun p => η p • G p) = G := by
    funext p
    by_cases hz : G p = 0
    · simp only [hz,smul_zero]
    · rw [(h1 p (subset_tsupport G hz)).self_of_nhds,one_smul]
  have hcut2 : (fun p => (η p)^2 • G p) = G := by
    funext p
    by_cases hz : G p = 0
    · simp only [hz,smul_zero]
    · rw [(h1 p (subset_tsupport G hz)).self_of_nhds,one_pow,one_smul]
  have hder (p v : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :
      (fderiv ℝ η p v) • G p = 0 := by
    by_cases hz : G p = 0
    · simp only [hz,smul_zero]
    · rw [(h1 p (subset_tsupport G hz)).fderiv_eq]
      simp
  have hError : grushinCutoffEnergy c η G = 0 := by
    unfold grushinCutoffEnergy partialYDirectional partialTDirectional
    simp only [hder,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,mul_zero,integral_zero,Finset.sum_const_zero,add_zero]
  have he := compact_cutoff_grushin_energy c hη hcη hG
  rw [hcut,hError,add_zero] at he
  apply he.trans
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p =>
    congrArg (fun z : ℂ => inner ℝ z (euclideanGrushin c G p)) (congrFun hcut2 p))

theorem grushin_gradient_energy_nonneg {c : ℝ} (hc : 0 ≤ c)
    (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ) :
    0 ≤ grushinGradientEnergy c G := by
  unfold grushinGradientEnergy
  exact add_nonneg
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
    (mul_nonneg hc (Finset.sum_nonneg (fun _ _ =>
      integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))

theorem grushin_y_gradient_le_energy {c : ℝ} (hc : 0 ≤ c)
    (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ) :
    (∑ i : ι, ∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) ≤
      grushinGradientEnergy c G := by
  unfold grushinGradientEnergy
  exact le_add_of_nonneg_right
    (mul_nonneg hc (Finset.sum_nonneg (fun _ _ =>
      integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))

end TheoremT.Continuum
