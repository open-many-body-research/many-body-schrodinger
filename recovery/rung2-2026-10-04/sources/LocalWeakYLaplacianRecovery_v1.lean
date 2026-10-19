import LocalSpectatorDerivativeAlgebra_v1
import GrushinLaplacianTestRewrite_v1
import ProductLocalEllipticH2_v1

/-! Preliminary joint weak H2 for the finite Y-recovery schedule.
The negative Y-Laplacian equation and genuine raw local first/second spectator
jets imply the actual full product Laplacian equation. No Y derivative is
assumed. Spectator norms are not estimated in this qualitative prerequisite.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem LocalSpectatorD.second_test {Ω : Set (Space κ)}
    {f d e : Space κ → ℂ} {j : κ}
    (hd : LocalSpectatorD Ω f d j) (he : LocalSpectatorD Ω d e j)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    (∫ p, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j) • f p) =
      ∫ p, φ p • e p := by
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (tDir j)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hcDφ := hcφ.fderiv_apply ℝ (tDir j)
  have hsDφ := (tsupport_fderiv_apply_subset ℝ (tDir j)).trans hsφ
  rw [he φ hφ hcφ hsφ,hd _ hDφ hcDφ hsDφ,neg_neg]

set_option maxHeartbeats 800000 in
theorem local_y_to_product_laplacian_tests {Ω : Set (Space κ)}
    (f H : Space κ → ℂ) (d e : κ → Space κ → ℂ)
    (hf : ProductLocallyL2On f Ω) (hH : ProductLocallyL2On H Ω)
    (heL2 : ∀ j, ProductLocallyL2On (e j) Ω)
    (hd : ∀ j, LocalSpectatorD Ω f (d j) j)
    (he : ∀ j, LocalSpectatorD Ω (d j) (e j) j)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • H p)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    (∫ p, productFactorLaplacian (EuclideanSpace.basisFun (Fin 4) ℝ)
      (EuclideanSpace.basisFun κ ℝ) φ p • f p) =
      ∫ p, φ p • (-H p + ∑ j, e j p) := by
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  have hId (p : Space κ) : productFactorLaplacian (EuclideanSpace.basisFun (Fin 4) ℝ)
      (EuclideanSpace.basisFun κ ℝ) φ p =
      -splitGrushin 0 oscillatorBasis (fun _ => 0) φ p +
        ∑ j, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j) := by
    simpa only [hBasis,zero_mul,sub_zero,one_mul,tDir] using
      grushin_product_laplacian_test_identity 0 (EuclideanSpace.basisFun κ ℝ) φ p
  have hD (j : κ) : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (tDir j)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have iT (j : κ) : Integrable (fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j) • f p) :=
    product_locallyL2_compact_smul_integrable f hf
      (((hD j).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hcφ.fderiv_apply ℝ (tDir j)).fderiv_apply ℝ (tDir j))
      ((tsupport_fderiv_apply_subset ℝ (tDir j)).trans
        ((tsupport_fderiv_apply_subset ℝ (tDir j)).trans hsφ))
  have iP : Integrable (fun p => splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p) :=
    product_locallyL2_compact_smul_integrable f hf
      (splitGrushin_continuous 0 oscillatorBasis continuous_const hφ)
      (splitGrushin_compact 0 oscillatorBasis _ hcφ)
      ((splitGrushin_test_tsupport_subset 0 φ).trans hsφ)
  have iH := product_locallyL2_compact_smul_integrable H hH hφ.continuous hcφ hsφ
  have iE (j : κ) := product_locallyL2_compact_smul_integrable (e j) (heL2 j)
    hφ.continuous hcφ hsφ
  have iNegP : Integrable (fun p : Space κ =>
      -(splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p)) := iP.neg
  have iSumT : Integrable (fun p : Space κ =>
      ∑ j, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j) • f p) :=
    integrable_finsetSum _ (fun j _ => iT j)
  have iNegH : Integrable (fun p : Space κ => -(φ p • H p)) := iH.neg
  have iSumE : Integrable (fun p : Space κ => ∑ j, φ p • e j p) :=
    integrable_finsetSum _ (fun j _ => iE j)
  calc
    _ = -(∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p) +
        ∑ j, ∫ p, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j) • f p := by
      simp only [hId,add_smul,neg_smul,Finset.sum_smul]
      rw [integral_add iNegP iSumT,integral_neg,
        integral_finsetSum _ (fun j _ => iT j)]
    _ = -(∫ p, φ p • H p) + ∑ j, ∫ p, φ p • e j p := by
      rw [hP φ hφ hcφ hsφ]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => (hd j).second_test (he j) hφ hcφ hsφ)
    _ = _ := by
      rw [← integral_neg,← integral_finsetSum _ (fun j _ => iE j),
        ← integral_add iNegH iSumE]
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [smul_add,smul_neg,Finset.smul_sum]

set_option maxHeartbeats 800000 in
theorem local_y_laplacian_h2_of_spectator_jets {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    (f H : Space κ → ℂ) (d e : κ → Space κ → ℂ)
    (hf : ProductLocallyL2On f Ω) (hH : ProductLocallyL2On H Ω)
    (_hdL2 : ∀ j, ProductLocallyL2On (d j) Ω)
    (heL2 : ∀ j, ProductLocallyL2On (e j) Ω)
    (hd : ∀ j, LocalSpectatorD Ω f (d j) j)
    (he : ∀ j, LocalSpectatorD Ω (d j) (e j) j)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • H p) :
    ProductLocalWeakH2On f Ω := by
  apply product_local_elliptic_h2_on (EuclideanSpace.basisFun (Fin 4) ℝ)
    (EuclideanSpace.basisFun κ ℝ) hΩ f (fun p => -H p + ∑ j, e j p) hf
  · intro K hK hs
    exact (hH K hK hs).neg.add (memLp_finsetSum _ (fun j _ => heL2 j K hK hs))
  · intro φ hφ hcφ hsφ
    exact local_y_to_product_laplacian_tests f H d e hf hH heL2 hd he hP hφ hcφ hsφ

#print axioms LocalSpectatorD.second_test
#print axioms local_y_to_product_laplacian_tests
#print axioms local_y_laplacian_h2_of_spectator_jets
end TheoremT.Continuum.WeakGrushin
