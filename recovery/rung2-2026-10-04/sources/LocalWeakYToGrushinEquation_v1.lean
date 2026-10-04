import LocalWeakGrushinYEquation_v1
import GrushinLocalPotentialReduction_v1

/-! Recover the actual weak Grushin potential equation from the weak
negative-Y-Laplacian equation and genuine first and second spectator jets.
The minus sign on the recovered spectator trace is fixed by the operator.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem local_y_to_grushin_potential_equation
    (c : ℝ) {Ω : Set (Space κ)} {B : Space κ → ℝ} (hB : ContinuousOn B Ω)
    (f H : Space κ → ℂ) (d e : κ → Space κ → ℂ)
    (hf : ProductLocallyL2On f Ω) (hH : ProductLocallyL2On H Ω)
    (hd : ∀ j, ProductLocalWeakDirectional Ω f (d j) (tDir j))
    (he : ∀ j, ProductLocalWeakDirectional Ω (d j) (e j) (tDir j))
    (hP0 : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • H p) :
    ProductLocallyL2On (fun p => H p-(c*‖p.1‖^2) • (∑ j, e j p)+B p • f p) Ω ∧
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      Integrable (fun p => splitGrushin c oscillatorBasis B φ p • f p) ∧
      Integrable (fun p => φ p • (H p-(c*‖p.1‖^2) • (∑ j, e j p)+B p • f p)) ∧
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) =
        ∫ p, φ p • (H p-(c*‖p.1‖^2) • (∑ j, e j p)+B p • f p) := by
  have hTrace : ProductLocallyL2On (fun p => ∑ j, e j p) Ω := by
    intro K hK hs
    exact memLp_finsetSum _ (fun j _ => (he j).2.1 K hK hs)
  have hWeight : ProductLocallyL2On
      (fun p : Space κ => (c*‖p.1‖^2) • (∑ j, e j p)) Ω :=
    product_locallyL2On_smul_of_continuousOn
      (continuous_const.mul (continuous_fst.norm.pow 2)).continuousOn hTrace
  have hPot : ProductLocallyL2On (fun p => B p • f p) Ω :=
    product_locallyL2On_smul_of_continuousOn hB hf
  have hRaw : ProductLocallyL2On
      (fun p => H p-(c*‖p.1‖^2) • (∑ j, e j p)) Ω :=
    product_locallyL2On_sub hH hWeight
  have hSource : ProductLocallyL2On
      (fun p => H p-(c*‖p.1‖^2) • (∑ j, e j p)+B p • f p) Ω := by
    intro K hK hs
    exact (hRaw K hK hs).add (hPot K hK hs)
  refine ⟨hSource,?_⟩
  intro φ hφ hc hs
  have iP (b : ℝ) : Integrable
      (fun p => splitGrushin b oscillatorBasis (fun _ => 0) φ p • f p) :=
    product_raw_locallyL2_compact_smul_integrable hf
      (splitGrushin_continuous b oscillatorBasis continuous_const hφ)
      (splitGrushin_compact b oscillatorBasis _ hc)
      ((splitGrushin_test_tsupport_subset b φ).trans hs)
  have iH := product_raw_locallyL2_compact_smul_integrable hH hφ.continuous hc hs
  have iW := product_raw_locallyL2_compact_smul_integrable hWeight hφ.continuous hc hs
  have hA : ContDiff ℝ ∞ (fun y : KSSpace => c*‖y‖^2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hw (j : κ) := local_spectator_invariant_weight_second_test
    (hd j) (he j) hA hφ hc hs
  have iSumT : Integrable (fun p => ∑ j, (c*‖p.1‖^2 *
      fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j)) • f p) :=
    integrable_finsetSum _ (fun j _ => (hw j).2.1)
  have hSplit : (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • f p) =
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p)+
        ∫ p, φ p • ((c*‖p.1‖^2) • (∑ j, e j p)) := by
    simp only [grushin_y_test_identity c φ,add_smul,Finset.mul_sum,Finset.sum_smul]
    rw [integral_add (iP c) iSumT,integral_finsetSum _ (fun j _ => (hw j).2.1)]
    congr 1
    simp only [Finset.smul_sum]
    rw [integral_finsetSum _ (fun j _ => by
      simpa only [smul_smul,mul_comm] using (hw j).1)]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [smul_smul,mul_comm] using (hw j).2.2
  have hPrincipal : (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) =
      ∫ p, φ p • (H p-(c*‖p.1‖^2) • (∑ j, e j p)) := by
    simp only [smul_sub]
    rw [integral_sub iH iW]
    rw [hP0 φ hφ hc hs] at hSplit
    exact eq_sub_of_add_eq hSplit.symm
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  have hi := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
    hB f (fun p => H p-(c*‖p.1‖^2) • (∑ j, e j p)+B p • f p)
    hf hSource hφ hc hs
  rw [hBasis] at hi
  have hEq := hi.mpr (by simpa only [add_sub_cancel_right] using hPrincipal)
  refine ⟨?_,product_raw_locallyL2_compact_smul_integrable hSource hφ.continuous hc hs,hEq⟩
  have hInt := (grushin_local_potential_test_integrable c (EuclideanSpace.basisFun κ ℝ)
    hB f (fun p => H p-(c*‖p.1‖^2) • (∑ j, e j p)+B p • f p)
    hf hSource hφ hc hs).1
  rw [hBasis] at hInt
  exact hInt

#print axioms local_y_to_grushin_potential_equation
end TheoremT.Continuum.WeakGrushin
