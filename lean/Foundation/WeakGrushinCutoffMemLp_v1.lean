import WeakGrushinCutoffAlgebra_v1

/-! The actual weak cutoff errors, including their Grushin weight, belong to
L2. Compact support of the smooth cutoff bounds each differentiated scalar
coefficient; the input function and first jets need only belong to L2. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_cutoff_weighted_first_memLp
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (a : Space κ → ℝ) (ha : Continuous a) (v : Space κ)
    (f : Lp ℂ 2 (volume : Measure (Space κ))) :
    MemLp (fun p => (a p*fderiv ℝ χ p v) • f p) 2 volume := by
  have hd : Continuous (fun p => fderiv ℝ χ p v) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (Lp.memLp f).smul ((ha.mul hd).memLp_top_of_hasCompactSupport
    ((hc.fderiv_apply ℝ v).mul_left) volume)

theorem compact_cutoff_weighted_second_memLp
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (a : Space κ → ℝ) (ha : Continuous a) (v w : Space κ)
    (f : Lp ℂ 2 (volume : Measure (Space κ))) :
    MemLp (fun p => (a p*fderiv ℝ (fun q => fderiv ℝ χ q v) p w) • f p) 2 volume := by
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  exact compact_cutoff_weighted_first_memLp hd (hc.fderiv_apply ℝ v) a ha w f

theorem cutoffYError_memLp
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    MemLp (cutoffYError χ f d) 2 volume := by
  apply memLp_finsetSum
  intro i hi
  have h1 := compact_cutoff_weighted_second_memLp hχ hc (fun _ => 1)
    continuous_const (yDir i) (yDir i) f
  have h2 := compact_cutoff_weighted_first_memLp hχ hc (fun _ => 2)
    continuous_const (yDir i) (d (yDir i))
  simpa only [Pi.add_def,one_mul] using h1.add h2

theorem cutoffTError_memLp
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    MemLp (cutoffTError χ f d) 2 volume := by
  apply memLp_finsetSum
  intro j hj
  have h1 := compact_cutoff_weighted_second_memLp hχ hc (fun _ => 1)
    continuous_const (tDir j) (tDir j) f
  have h2 := compact_cutoff_weighted_first_memLp hχ hc (fun _ => 2)
    continuous_const (tDir j) (d (tDir j))
  simpa only [Pi.add_def,one_mul] using h1.add h2

theorem weighted_cutoffTError_memLp (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    MemLp (fun p => (c*‖p.1‖^2) • cutoffTError χ f d p) 2 volume := by
  have ha : Continuous (fun p : Space κ => c*‖p.1‖^2) := by fun_prop
  have hb : Continuous (fun p : Space κ => (c*‖p.1‖^2)*2) := ha.mul continuous_const
  simp only [cutoffTError,Finset.smul_sum,smul_add,← mul_smul]
  apply memLp_finsetSum
  intro j hj
  have h1 := compact_cutoff_weighted_second_memLp hχ hc (fun p => c*‖p.1‖^2)
    ha (tDir j) (tDir j) f
  have h2 := compact_cutoff_weighted_first_memLp hχ hc (fun p => (c*‖p.1‖^2)*2)
    hb (tDir j) (d (tDir j))
  simpa only [Pi.add_def,mul_assoc] using h1.add h2

#print axioms compact_cutoff_weighted_first_memLp
#print axioms compact_cutoff_weighted_second_memLp
#print axioms cutoffYError_memLp
#print axioms cutoffTError_memLp
#print axioms weighted_cutoffTError_memLp
end TheoremT.Continuum.WeakGrushin
