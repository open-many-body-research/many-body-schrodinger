import GrushinHoleCommutator_v1
import NuclearKSLift_v1

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ksHoleCommutator_zero_off_test {φ : KSSpace × F → ℝ}
    {q : KSSpace × F} (hq : q ∉ tsupport φ) (δ : ℝ) :
    ksHoleCommutator δ φ q=0 := by
  simp [ksHoleCommutator,image_eq_zero_of_notMem_tsupport hq,fderiv_of_notMem_tsupport ℝ hq]

theorem ksHoleCommutator_continuous (δ : ℝ) {φ : KSSpace × F → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : Continuous (ksHoleCommutator δ φ) := by
  have hh := ksHole_contDiff δ
  have h1 (k : Fin 4) : ContDiff ℝ ∞ (fun y => fderiv ℝ (ksHole δ) y (ksBasis k)) :=
    (hh.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have h2 (k : Fin 4) : Continuous
      (fun y => fderiv ℝ (fun x => fderiv ℝ (ksHole δ) x (ksBasis k)) y (ksBasis k)) :=
    (((h1 k).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  have hd (k : Fin 4) : Continuous (fun q : KSSpace × F => fderiv ℝ φ q (ksBasis k,0)) :=
    ((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  apply Continuous.neg
  apply continuous_finset_sum
  intro k hk
  exact ((h2 k).comp continuous_fst |>.mul hφ.continuous).add
    ((continuous_const.mul ((h1 k).continuous.comp continuous_fst)).mul (hd k))

theorem ksHoleCommutator_compact (δ : ℝ) {φ : KSSpace × F → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (ksHoleCommutator δ φ) := by
  apply hc.mono'
  intro q hq
  by_contra hn
  exact hq (ksHoleCommutator_zero_off_test hn δ)

theorem nuclear_KS_commutator_tube_support {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (q : NuclearKSSpace i)
    (hq : q ∉ (Metric.ball (0 : KSSpace) (3*δ)) ×ˢ (Prod.snd '' tsupport φ)) :
    ksHoleCommutator δ φ q=0 := by
  by_cases ht : q ∈ tsupport φ
  · have hs : q.2 ∈ Prod.snd '' tsupport φ := ⟨q,ht,rfl⟩
    have hy : 3*δ ≤ ‖q.1‖ := by
      by_contra hn
      apply hq
      exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using lt_of_not_ge hn,hs⟩
    exact ksHoleCommutator_zero_outer hδ φ (by linarith)
  · exact ksHoleCommutator_zero_off_test ht δ

#print axioms nuclear_KS_commutator_tube_support
#print axioms ksHoleCommutator_compact
end TheoremT.Continuum
