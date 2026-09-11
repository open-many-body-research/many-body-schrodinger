import GrushinCommutatorSupport_v1

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

theorem splitGrushin_continuous (c : ℝ) (v : ι → F) {B : KSSpace × F → ℝ}
    (hB : Continuous B) {φ : KSSpace × F → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (splitGrushin c v B φ) := by
  have h2 (w : KSSpace × F) : Continuous (fun q => fderiv ℝ (fun x => fderiv ℝ φ x w) q w) :=
    ((((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  exact ((continuous_finsetSum _ (fun k _ => h2 (ksBasis k,0))).neg.sub
    ((continuous_const.mul (continuous_fst.norm.pow 2)).mul
      (continuous_finsetSum _ (fun j _ => h2 (0,v j))))).add (hB.mul hφ.continuous)

theorem splitGrushin_zero_off_test (c : ℝ) (v : ι → F) (B : KSSpace × F → ℝ)
    {φ : KSSpace × F → ℝ} {q : KSSpace × F} (hq : q ∉ tsupport φ) :
    splitGrushin c v B φ q=0 := by
  have hd (w : KSSpace × F) : q ∉ tsupport (fun x => fderiv ℝ φ x w) :=
    fun h => hq (tsupport_fderiv_apply_subset ℝ w h)
  simp [splitGrushin,image_eq_zero_of_notMem_tsupport hq,
    fun w => fderiv_of_notMem_tsupport ℝ (hd w)]

theorem splitGrushin_compact (c : ℝ) (v : ι → F) (B : KSSpace × F → ℝ)
    {φ : KSSpace × F → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (splitGrushin c v B φ) := by
  apply hc.mono'
  intro q hq
  by_contra hn
  exact hq (splitGrushin_zero_off_test c v B hn)

#print axioms splitGrushin_compact
end TheoremT.Continuum
