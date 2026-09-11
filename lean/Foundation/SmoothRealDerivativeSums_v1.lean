import RegularizedCoulombCusp_v1

noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem real_fderiv_finset_sum_apply {N : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → Configuration N → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (x v : Configuration N) :
    fderiv ℝ (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, fderiv ℝ (f i) x v := by
  rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) x)]
  simp

theorem real_fderiv_const_mul_apply {N : ℕ} {f : Configuration N → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x v : Configuration N) :
    fderiv ℝ (fun y => c*f y) x v = c*fderiv ℝ f x v := by
  have hh := (hasFDerivAt_const c x).mul ((hf.differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt (fun y => c*f y) _ x at hh
  rw [hh.fderiv]
  simp

theorem real_fderiv_add_apply {N : ℕ} {f g : Configuration N → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v : Configuration N) :
    fderiv ℝ (fun y => f y+g y) x v = fderiv ℝ f x v+fderiv ℝ g x v := by
  change fderiv ℝ (f+g) x v = _
  rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp

theorem real_mixed_finset_sum_apply {N : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → Configuration N → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (x v w : Configuration N) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => ∑ i ∈ s, f i z) y v) x w =
      ∑ i ∈ s, fderiv ℝ (fun y => fderiv ℝ (f i) y v) x w := by
  simp_rw [real_fderiv_finset_sum_apply s hf]
  apply real_fderiv_finset_sum_apply
  intro i hi
  exact ((hf i hi).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const


theorem real_mixed_const_mul_apply {N : ℕ} {f : Configuration N → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x v w : Configuration N) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => c*f z) y v) x w =
      c*fderiv ℝ (fun y => fderiv ℝ f y v) x w := by
  simp_rw [real_fderiv_const_mul_apply hf c]
  apply real_fderiv_const_mul_apply
  exact (hf.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem real_mixed_add_apply {N : ℕ} {f g : Configuration N → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : Configuration N) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f z+g z) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y v) x w+fderiv ℝ (fun y => fderiv ℝ g y v) x w := by
  simp_rw [real_fderiv_add_apply hf hg]
  exact real_fderiv_add_apply
    ((hf.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
    ((hg.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const) x w

#print axioms real_mixed_finset_sum_apply
end TheoremT.Continuum
