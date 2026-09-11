import WeakGrushinJetFields_v1
import WeakProductSecondTest_v1
import GrushinTestSupport_v1
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Exact compact-test identification of the Grushin expression formed from
genuine weak H2 jets. No compact support of the input is needed for this test
identity; polynomial spectator weights preserve local integrability. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def diagonalDir : Fin 4 ⊕ κ → Space κ
  | .inl i => yDir i
  | .inr j => tDir j

theorem principalWeight_contDiff (c : ℝ) (i : Fin 4 ⊕ κ) :
    ContDiff ℝ ∞ (principalWeight c i) := by
  cases i with
  | inl i => exact contDiff_const
  | inr j =>
    change ContDiff ℝ ∞ (fun p : Space κ => -(c*‖p.1‖^2))
    exact (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst)).neg

theorem principal_test_pointwise (c : ℝ) (φ : Space κ → ℝ) (p : Space κ) :
    splitGrushin c oscillatorBasis (fun _ => 0) φ p =
      ∑ i : Fin 4 ⊕ κ, principalWeight c i p *
        fderiv ℝ (fun z => fderiv ℝ φ z (diagonalDir i)) p (diagonalDir i) := by
  simp only [Fintype.sum_sum_type,principalWeight,diagonalDir,yDir,tDir,
    splitGrushin,oscillatorBasis,EuclideanSpace.single,ksBasis,
    neg_mul,one_mul,zero_mul,add_zero,Finset.sum_neg_distrib, ← Finset.mul_sum,sub_eq_add_neg]
  rfl

theorem principal_diagonal_test (c : ℝ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (i : Fin 4 ⊕ κ) :
    (∫ p, (principalWeight c i p * φ p) • diagonalJet e i p) =
      ∫ p, (principalWeight c i p * fderiv ℝ
        (fun z => fderiv ℝ φ z (diagonalDir i)) p (diagonalDir i)) • f p := by
  cases i with
  | inl i =>
    have hh := weakProduct_second_same_test (hd (yDir i)) (he (yDir i) (yDir i)) hφ hc
    simpa only [principalWeight,diagonalJet,diagonalDir,neg_one_mul,neg_smul,integral_neg]
      using congrArg Neg.neg hh
  | inr j =>
    exact spectator_invariant_weight_second_test (hd (tDir j)) (he (tDir j) (tDir j))
      (a := fun y => -(c*‖y‖^2)) ((contDiff_const.mul (contDiff_norm_sq ℝ)).neg) hφ hc

theorem principal_locallyIntegrable (c : ℝ) (e : Jet κ) :
    LocallyIntegrable (principal c e) volume := by
  have hh : LocallyIntegrable
      (fun p => ∑ i : Fin 4 ⊕ κ, principalWeight c i p • diagonalJet e i p) volume :=
    locallyIntegrable_finsetSum _ (fun i _ =>
      LocallyIntegrable.continuous_smul (principalWeight_continuous c i)
        ((Lp.memLp (diagonalJet e i)).locallyIntegrable (by norm_num)))
  simpa only [← principal_eq_finite_weighted] using hh

theorem principal_compact_test (c : ℝ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, φ p • principal c e p) =
      ∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p := by
  have iE (i : Fin 4 ⊕ κ) : Integrable
      (fun p => (principalWeight c i p * φ p) • diagonalJet e i p) :=
    ((Lp.memLp (diagonalJet e i)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((principalWeight_continuous c i).mul hφ.continuous) hc.mul_left
  have hD (i : Fin 4 ⊕ κ) : ContDiff ℝ ∞
      (fun p => fderiv ℝ φ p (diagonalDir i)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have iD (i : Fin 4 ⊕ κ) : Integrable (fun p =>
      (principalWeight c i p * fderiv ℝ
        (fun z => fderiv ℝ φ z (diagonalDir i)) p (diagonalDir i)) • f p) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((principalWeight_continuous c i).mul
        (((hD i).continuous_fderiv (by simp)).clm_apply continuous_const))
      (((hc.fderiv_apply ℝ (diagonalDir i)).fderiv_apply ℝ (diagonalDir i)).mul_left)
  calc
    _ = ∫ p, ∑ i : Fin 4 ⊕ κ, (principalWeight c i p * φ p) • diagonalJet e i p := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [principal_eq_finite_weighted,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul,mul_comm]
    _ = ∑ i : Fin 4 ⊕ κ, ∫ p, (principalWeight c i p * φ p) • diagonalJet e i p :=
      integral_finset_sum _ (fun i _ => iE i)
    _ = ∑ i : Fin 4 ⊕ κ, ∫ p, (principalWeight c i p * fderiv ℝ
        (fun z => fderiv ℝ φ z (diagonalDir i)) p (diagonalDir i)) • f p := by
      apply Finset.sum_congr rfl
      intro i _
      exact principal_diagonal_test c d e hd he hφ hc i
    _ = ∫ p, ∑ i : Fin 4 ⊕ κ, (principalWeight c i p * fderiv ℝ
        (fun z => fderiv ℝ φ z (diagonalDir i)) p (diagonalDir i)) • f p :=
      (integral_finset_sum _ (fun i _ => iD i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [← Finset.sum_smul,← principal_test_pointwise]

theorem principal_ae_eq_of_weak_output (c : ℝ)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    principal c e =ᵐ[volume] h := by
  apply ae_eq_of_integral_contDiff_smul_eq (principal_locallyIntegrable c e)
    ((Lp.memLp h).locallyIntegrable (by norm_num))
  intro φ hφ hc
  exact (principal_compact_test c d e hd he hφ hc).trans (hP φ hφ hc)

end TheoremT.Continuum.WeakGrushin
