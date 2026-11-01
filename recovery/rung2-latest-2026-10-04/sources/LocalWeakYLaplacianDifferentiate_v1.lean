import LocalProductDirectionalWeakAlgebra_v1
import WeakGrushinSpectatorSmoothCommute_v1
import WeakGrushinSpectatorTestData_v1

/-! Constant-direction differentiation of the actual negative Y-Laplacian
equation. Both solution and source derivatives are genuine local weak
derivatives with local L2 membership. The differentiated equation is derived
against every compact smooth test, in any constant product-space direction. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem splitGrushin_zero_directional_commute (v : Space κ)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : Space κ) :
    splitGrushin 0 oscillatorBasis (fun _ => 0) (fun q => fderiv ℝ φ q v) p =
      fderiv ℝ (splitGrushin 0 oscillatorBasis (fun _ => 0) φ) p v := by
  let Ly := fun q : Space κ => ∑ i : Fin 4,
    fderiv ℝ (fun z => fderiv ℝ φ z (ksBasis i,0)) q (ksBasis i,0)
  have h2 (i : Fin 4) : ContDiff ℝ ∞
      (fun q => fderiv ℝ (fun z => fderiv ℝ φ z (ksBasis i,0)) q (ksBasis i,0)) :=
    ((((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
  have hy : ContDiff ℝ ∞ Ly := ContDiff.sum (fun i _ => h2 i)
  have heq : splitGrushin 0 oscillatorBasis (fun _ => 0) φ = (fun q => -Ly q) := by
    funext q
    simp only [splitGrushin,Ly,zero_mul,sub_zero,add_zero]
  have hD := (hy.differentiable (by simp) p).hasFDerivAt.neg
  change HasFDerivAt (𝕜 := ℝ) (fun q => -Ly q) _ p at hD
  rw [heq,hD.fderiv]
  simp only [neg_apply]
  have hyD := finite_second_sum_directional_commute
    (fun i : Fin 4 => (ksBasis i,(0 : EuclideanSpace ℝ κ))) hφ p v
  change fderiv ℝ Ly p v = _ at hyD
  rw [hyD]
  simp only [splitGrushin,zero_mul,sub_zero,add_zero]

theorem local_weak_y_laplacian_differentiate
    {Ω : Set (Space κ)} {f df H dH : Space κ → ℂ} {v : Space κ}
    (hD : ProductLocalWeakDirectional Ω f df v)
    (hHD : ProductLocalWeakDirectional Ω H dH v)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • H p) :
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Integrable (fun p => splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • df p) ∧
      Integrable (fun p => φ p • dH p) ∧
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • df p) = ∫ p, φ p • dH p := by
  intro φ hφ hcφ hsφ
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hcDφ := hcφ.fderiv_apply ℝ v
  have hsDφ := (tsupport_fderiv_apply_subset ℝ v).trans hsφ
  have hPφ := splitGrushin_zero_contDiff 0 oscillatorBasis hφ
  have hcPφ := splitGrushin_compact 0 oscillatorBasis (fun _ => 0) hcφ
  have hsPφ := (splitGrushin_test_tsupport_subset 0 φ).trans hsφ
  refine ⟨(hD.test_integrable hPφ hcPφ hsPφ).1,
    (hHD.test_integrable hφ hcφ hsφ).1,?_⟩
  calc
    _ = -(∫ p, fderiv ℝ (splitGrushin 0 oscillatorBasis (fun _ => 0) φ) p v • f p) :=
      hD.2.2 _ hPφ hcPφ hsPφ
    _ = -(∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0)
        (fun q => fderiv ℝ φ q v) p • f p) := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => congrArg (fun a : ℝ => a • f p)
        (splitGrushin_zero_directional_commute v hφ p).symm)
    _ = -(∫ p, fderiv ℝ φ p v • H p) := congrArg Neg.neg (hP _ hDφ hcDφ hsDφ)
    _ = _ := (hHD.2.2 φ hφ hcφ hsφ).symm

end TheoremT.Continuum.WeakGrushin
