import WeakProductSecondTest_v1
import ProductCompactTestTransport_v2
import GrushinTestSupport_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {κ : Type*} [Fintype κ]

theorem grushin_product_laplacian_test_identity (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    (φ : KSSpace × T → ℝ) (p : KSSpace × T) :
    productFactorLaplacian (EuclideanSpace.basisFun (Fin 4) ℝ) b φ p =
      -splitGrushin c b (fun _ => 0) φ p +
      (1-c*‖p.1‖^2)*(∑ j, fderiv ℝ (fun q => fderiv ℝ φ q (0,b j)) p (0,b j)) := by
  simp only [productFactorLaplacian,splitGrushin,EuclideanSpace.basisFun_apply,
    EuclideanSpace.single,PiLp.single,ksBasis]
  ring

theorem grushin_to_product_laplacian_tests
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    (f h : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (d e : κ → Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (hd : ∀ j, WeakProductL2Directional f (d j) (0,b j))
    (he : ∀ j, WeakProductL2Directional (d j) (e j) (0,b j))
    {Ω : Set (KSSpace × T)}
    (hP : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    {φ : KSSpace × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    (∫ p, productFactorLaplacian (EuclideanSpace.basisFun (Fin 4) ℝ) b φ p • f p) =
      ∫ p, φ p • (-h p + (1-c*‖p.1‖^2) • (∑ j, e j p)) := by
  let a : KSSpace → ℝ := fun y => 1-c*‖y‖^2
  have ha : ContDiff ℝ ∞ a := contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
  have hA : ContDiff ℝ ∞ (fun p : KSSpace × T => a p.1) := ha.comp contDiff_fst
  have hDj (j : κ) : ContDiff ℝ ∞ (fun p : KSSpace × T => fderiv ℝ φ p (0,b j)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hTj (j : κ) : Continuous (fun p : KSSpace × T =>
      a p.1 * fderiv ℝ (fun q => fderiv ℝ φ q (0,b j)) p (0,b j)) :=
    hA.continuous.mul (((hDj j).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcTj (j : κ) : HasCompactSupport (fun p : KSSpace × T =>
      a p.1 * fderiv ℝ (fun q => fderiv ℝ φ q (0,b j)) p (0,b j)) :=
    ((hc.fderiv_apply ℝ (0,b j)).fderiv_apply ℝ (0,b j)).mul_left
  have iT (j : κ) : Integrable (fun p =>
      (a p.1 * fderiv ℝ (fun q => fderiv ℝ φ q (0,b j)) p (0,b j)) • f p) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (hTj j) (hcTj j)
  have iE (j : κ) : Integrable (fun p => (a p.1 * φ p) • e j p) :=
    ((Lp.memLp (e j)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (hA.continuous.mul hφ.continuous) hc.mul_left
  have iP : Integrable (fun p => splitGrushin c b (fun _ => 0) φ p • f p) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (splitGrushin_continuous c b continuous_const hφ) (splitGrushin_compact c b _ hc)
  have iH : Integrable (fun p => φ p • h p) :=
    ((Lp.memLp h).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hc
  have isum : Integrable (fun p => ∑ j, (a p.1 * fderiv ℝ
      (fun q => fderiv ℝ φ q (0,b j)) p (0,b j)) • f p) :=
    integrable_finset_sum _ (fun j _ => iT j)
  have iesum : Integrable (fun p => ∑ j, (a p.1 * φ p) • e j p) :=
    integrable_finset_sum _ (fun j _ => iE j)
  calc
    (∫ p, productFactorLaplacian (EuclideanSpace.basisFun (Fin 4) ℝ) b φ p • f p) = -(∫ p, splitGrushin c b (fun _ => 0) φ p • f p) +
        ∑ j, ∫ p, (a p.1 * fderiv ℝ (fun q => fderiv ℝ φ q (0,b j)) p (0,b j)) • f p := by
      simp only [grushin_product_laplacian_test_identity c b φ,add_smul,neg_smul,
        Finset.mul_sum,Finset.sum_smul]
      have hin : Integrable (fun p => -(splitGrushin c b (fun _ => 0) φ p • f p)) := iP.neg
      rw [integral_add hin isum,integral_neg,integral_finset_sum _ (fun j _ => iT j)]
    _ = -(∫ p, φ p • h p) + ∑ j, ∫ p, (a p.1 * φ p) • e j p := by
      rw [hP φ hφ hc hs]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact (spectator_invariant_weight_second_test (hd j) (he j) ha hφ hc).symm
    _ = _ := by
      rw [← integral_neg,← integral_finset_sum _ (fun j _ => iE j)]
      have hin : Integrable (fun p => -(φ p • h p)) := iH.neg
      rw [← integral_add hin iesum]
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [smul_add,smul_neg,Finset.smul_sum,← mul_smul]
      dsimp [a]
      rw [mul_comm (φ p) (1-c*‖p.1‖^2)]

#print axioms grushin_product_laplacian_test_identity
#print axioms grushin_to_product_laplacian_tests
end TheoremT.Continuum
