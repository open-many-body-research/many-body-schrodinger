import KSHoleCutoff_v1
import KSMapHessian_v1
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def ksBasePartial (k : Fin 4) (x : KSSpace) : ℝ := fderiv ℝ ksCutoffBase x (ksBasis k)

theorem ksBasePartial_contDiff (k : Fin 4) : ContDiff ℝ ∞ (ksBasePartial k) :=
  (ksCutoffBase.contDiff.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem ksBasePartial_compact (k : Fin 4) : HasCompactSupport (ksBasePartial k) :=
  ksCutoffBase.hasCompactSupport.fderiv_apply ℝ (ksBasis k)

theorem ksHole_partial (δ : ℝ) (x : KSSpace) (k : Fin 4) :
    fderiv ℝ (ksHole δ) x (ksBasis k) = -δ⁻¹*ksBasePartial k (δ⁻¹ • x) := by
  have hbc : ContDiff ℝ ∞ (ksCutoffBase : KSSpace → ℝ) := ksCutoffBase.contDiff
  have hb := (hbc.differentiable (by simp) (δ⁻¹ • x)).hasFDerivAt
  have hs := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul δ⁻¹
  have hh := (hb.comp x hs).const_sub 1
  change HasFDerivAt (ksHole δ) _ x at hh
  rw [hh.fderiv]
  simp [ksBasePartial]

theorem ksHole_secondPartial (δ : ℝ) (x : KSSpace) (k l : Fin 4) :
    fderiv ℝ (fun y => fderiv ℝ (ksHole δ) y (ksBasis k)) x (ksBasis l) =
      -(δ⁻¹^2)*fderiv ℝ (ksBasePartial k) (δ⁻¹ • x) (ksBasis l) := by
  have he : (fun y => fderiv ℝ (ksHole δ) y (ksBasis k)) =
      (fun y => (-δ⁻¹) • ksBasePartial k (δ⁻¹ • y)) := by
    funext y
    exact ksHole_partial δ y k
  rw [he]
  have hb := ((ksBasePartial_contDiff k).differentiable (by simp) (δ⁻¹ • x)).hasFDerivAt
  have hs := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul δ⁻¹
  have hh := (hb.comp x hs).const_smul (-δ⁻¹)
  change HasFDerivAt (fun y => (-δ⁻¹) • ksBasePartial k (δ⁻¹ • y)) _ x at hh
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  ring

theorem ksHole_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ (x : KSSpace) (k : Fin 4),
      ‖fderiv ℝ (ksHole δ) x (ksBasis k)‖ ≤ C/δ := by
  have hbc : ContDiff ℝ ∞ (ksCutoffBase : KSSpace → ℝ) := ksCutoffBase.contDiff
  obtain ⟨C,hC⟩ := (ksCutoffBase.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hbc.continuous_fderiv (by simp))
  refine ⟨C,(norm_nonneg _).trans (hC 0),fun δ hδ x k => ?_⟩
  have hb : ‖ksBasePartial k (δ⁻¹ • x)‖ ≤ C := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    simpa [ksBasis] using hC (δ⁻¹ • x)
  rw [ksHole_partial,norm_mul,norm_neg,Real.norm_eq_abs,abs_inv,abs_of_pos hδ]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hδ.le)

theorem ksHole_secondDerivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ (x : KSSpace) (k l : Fin 4),
      ‖fderiv ℝ (fun y => fderiv ℝ (ksHole δ) y (ksBasis k)) x (ksBasis l)‖ ≤ C/δ^2 := by
  have hex (k : Fin 4) : ∃ C : ℝ, ∀ x, ‖fderiv ℝ (ksBasePartial k) x‖ ≤ C :=
    ((ksBasePartial_compact k).fderiv ℝ).exists_bound_of_continuous
      ((ksBasePartial_contDiff k).continuous_fderiv (by simp))
  choose C hC using hex
  have hC0 (k : Fin 4) : 0 ≤ C k := (norm_nonneg _).trans (hC k 0)
  refine ⟨∑ k,C k,Finset.sum_nonneg (fun k _ => hC0 k),fun δ hδ x k l => ?_⟩
  have hb : ‖fderiv ℝ (ksBasePartial k) (δ⁻¹ • x) (ksBasis l)‖ ≤ ∑ k,C k := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply le_trans _ (Finset.single_le_sum (fun k _ => hC0 k) (Finset.mem_univ k))
    simpa [ksBasis] using hC k (δ⁻¹ • x)
  rw [ksHole_secondPartial,norm_mul,norm_neg,norm_pow,Real.norm_eq_abs,abs_inv,abs_of_pos hδ]
  simpa only [div_eq_mul_inv,inv_pow,mul_comm] using mul_le_mul_of_nonneg_left hb (sq_nonneg δ⁻¹)

#print axioms ksHole_partial
#print axioms ksHole_secondPartial
#print axioms ksHole_derivative_bound
#print axioms ksHole_secondDerivative_bound
end TheoremT.Continuum
