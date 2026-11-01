import LocalProductDirectionalWeakAlgebra_v1
import LocalWeakYLaplacianRecovery_v1
import GrushinLaplacianTestRewrite_v1

/-! Extraction of the actual weak negative Y-Laplacian equation from the
raw local Grushin equation and genuine first and same-second spectator jets.
The new source has the plus sign h + c*norm(y)^2*sum(e). Compact-test
integrability and raw local L2 membership are proved. No global Lp or H2
membership is assumed or asserted by this extraction step.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {kappa : Type} [Fintype kappa] [DecidableEq kappa]

theorem local_spectator_invariant_weight_second_test
    {Omega : Set (Space kappa)} {f d e : Space kappa → ℂ} {j : kappa}
    (hd : ProductLocalWeakDirectional Omega f d (tDir j))
    (he : ProductLocalWeakDirectional Omega d e (tDir j))
    {a : KSSpace → ℝ} (ha : ContDiff ℝ ∞ a)
    {phi : Space kappa → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hcphi : HasCompactSupport phi) (hsphi : tsupport phi ⊆ Omega) :
    Integrable (fun p => (a p.1 * phi p) • e p) ∧
    Integrable (fun p => (a p.1 * fderiv ℝ
      (fun q => fderiv ℝ phi q (tDir j)) p (tDir j)) • f p) ∧
    (∫ p, (a p.1 * fderiv ℝ (fun q => fderiv ℝ phi q (tDir j)) p (tDir j)) • f p) =
      ∫ p, (a p.1 * phi p) • e p := by
  have hA : ContDiff ℝ ∞ (fun p : Space kappa => a p.1) := ha.comp contDiff_fst
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ phi p (tDir j)) :=
    (hphi.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have htest := LocalSpectatorD.second_test hd.2.2 he.2.2 (hA.mul hphi)
    hcphi.mul_left (tsupport_mul_subset_right.trans hsphi)
  have hfirst (p : Space kappa) :
      fderiv ℝ (fun q : Space kappa => a q.1) p (tDir j) = 0 := by
    change fderiv ℝ (fun q : Space kappa => a q.1) p (0,oscillatorBasis j) = 0
    rw [first_directional_fst (ha.differentiable (by simp))]
    simp
  have hsecond (p : Space kappa) : fderiv ℝ
      (fun q => fderiv ℝ (fun z : Space kappa => a z.1) q (tDir j)) p (tDir j) = 0 := by
    change fderiv ℝ (fun q => fderiv ℝ (fun z : Space kappa => a z.1)
      q (0,oscillatorBasis j)) p (0,oscillatorBasis j) = 0
    rw [second_directional_fst ha]
    simp
  simp only [second_directional_product hA hphi] at htest
  simp only [hsecond] at htest
  simp only [hfirst, zero_mul, zero_add, add_zero] at htest
  refine ⟨?_,?_,htest⟩
  · exact product_raw_locallyL2_compact_smul_integrable he.2.1
      (hA.continuous.mul hphi.continuous) hcphi.mul_left
      (tsupport_mul_subset_right.trans hsphi)
  · exact product_raw_locallyL2_compact_smul_integrable hd.1
      (hA.continuous.mul ((hD.continuous_fderiv (by simp)).clm_apply continuous_const))
      ((hcphi.fderiv_apply ℝ (tDir j)).fderiv_apply ℝ (tDir j)).mul_left
      (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (tDir j)).trans
        ((tsupport_fderiv_apply_subset ℝ (tDir j)).trans hsphi)))

theorem local_grushin_y_source_locallyL2 (c : ℝ)
    {Omega : Set (Space kappa)} {h : Space kappa → ℂ} {e : kappa → Space kappa → ℂ}
    (hh : ProductLocallyL2On h Omega)
    (he : ∀ j, ProductLocallyL2On (e j) Omega) :
    ProductLocallyL2On (fun p => h p + (c*‖p.1‖^2) • (∑ j, e j p)) Omega := by
  have hsum : ProductLocallyL2On (fun p => ∑ j, e j p) Omega := by
    intro K hK hs
    exact memLp_finsetSum _ (fun j _ => he j K hK hs)
  have hweight : ProductLocallyL2On
      (fun p => (c*‖p.1‖^2) • (∑ j, e j p)) Omega :=
    product_locallyL2On_smul_of_continuousOn
      (continuous_const.mul (continuous_fst.norm.pow 2)).continuousOn hsum
  intro K hK hs
  exact (hh K hK hs).add (hweight K hK hs)

theorem grushin_y_test_identity (c : ℝ) (phi : Space kappa → ℝ) (p : Space kappa) :
    splitGrushin 0 oscillatorBasis (fun _ => 0) phi p =
      splitGrushin c oscillatorBasis (fun _ => 0) phi p +
        (c*‖p.1‖^2) * (∑ j, fderiv ℝ
          (fun q => fderiv ℝ phi q (tDir j)) p (tDir j)) := by
  simp only [splitGrushin, tDir]
  ring

set_option maxHeartbeats 800000 in
theorem local_grushin_to_y_equation (c : ℝ)
    {Omega : Set (Space kappa)} (f h : Space kappa → ℂ)
    (d e : kappa → Space kappa → ℂ)
    (hf : ProductLocallyL2On f Omega) (hh : ProductLocallyL2On h Omega)
    (hd : ∀ j, ProductLocalWeakDirectional Omega f (d j) (tDir j))
    (he : ∀ j, ProductLocalWeakDirectional Omega (d j) (e j) (tDir j))
    (hP : ∀ phi : Space kappa → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Omega →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) phi p • f p) = ∫ p, phi p • h p) :
    ProductLocallyL2On (fun p => h p + (c*‖p.1‖^2) • (∑ j, e j p)) Omega ∧
    ∀ phi : Space kappa → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Omega →
      Integrable (fun p => splitGrushin 0 oscillatorBasis (fun _ => 0) phi p • f p) ∧
      Integrable (fun p => phi p • (h p + (c*‖p.1‖^2) • (∑ j, e j p))) ∧
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) phi p • f p) =
        ∫ p, phi p • (h p + (c*‖p.1‖^2) • (∑ j, e j p)) := by
  have hsource := local_grushin_y_source_locallyL2 c hh (fun j => (he j).2.1)
  refine ⟨hsource,?_⟩
  intro phi hphi hcphi hsphi
  have iP (b : ℝ) : Integrable
      (fun p => splitGrushin b oscillatorBasis (fun _ => 0) phi p • f p) :=
    product_raw_locallyL2_compact_smul_integrable hf
      (splitGrushin_continuous b oscillatorBasis continuous_const hphi)
      (splitGrushin_compact b oscillatorBasis _ hcphi)
      ((splitGrushin_test_tsupport_subset b phi).trans hsphi)
  have iH := product_raw_locallyL2_compact_smul_integrable hh hphi.continuous hcphi hsphi
  have iSource := product_raw_locallyL2_compact_smul_integrable hsource
    hphi.continuous hcphi hsphi
  have hA : ContDiff ℝ ∞ (fun y : KSSpace => c*‖y‖^2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hweighted (j : kappa) := local_spectator_invariant_weight_second_test
    (hd j) (he j) hA hphi hcphi hsphi
  have iSumT : Integrable (fun p => ∑ j, (c*‖p.1‖^2 *
      fderiv ℝ (fun q => fderiv ℝ phi q (tDir j)) p (tDir j)) • f p) :=
    integrable_finsetSum _ (fun j _ => (hweighted j).2.1)
  have iSumE : Integrable (fun p => ∑ j, (c*‖p.1‖^2 * phi p) • e j p) :=
    integrable_finsetSum _ (fun j _ => (hweighted j).1)
  refine ⟨iP 0,iSource,?_⟩
  calc
    _ = (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) phi p • f p) +
        ∑ j, ∫ p, (c*‖p.1‖^2 *
          fderiv ℝ (fun q => fderiv ℝ phi q (tDir j)) p (tDir j)) • f p := by
      simp only [grushin_y_test_identity c phi, add_smul, Finset.mul_sum, Finset.sum_smul]
      rw [integral_add (iP c) iSumT,
        integral_finsetSum _ (fun j _ => (hweighted j).2.1)]
    _ = (∫ p, phi p • h p) + ∑ j, ∫ p, (c*‖p.1‖^2 * phi p) • e j p := by
      rw [hP phi hphi hcphi hsphi]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => (hweighted j).2.2)
    _ = _ := by
      rw [← integral_finsetSum _ (fun j _ => (hweighted j).1),
        ← integral_add iH iSumE]
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [smul_add, Finset.smul_sum, ← mul_smul]
      rw [mul_comm (phi p) (c*‖p.1‖^2)]

end TheoremT.Continuum.WeakGrushin
