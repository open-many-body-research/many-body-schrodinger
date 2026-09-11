import KSMapGeometry_v1
import NuclearKSLift_v1
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Genuine smooth transverse hole cutoffs in the four-dimensional KS variable. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def ksCutoffBase : ContDiffBump (0 : KSSpace) := ⟨1,2,by norm_num,by norm_num⟩

def ksHole (δ : ℝ) (y : KSSpace) : ℝ := 1-ksCutoffBase (δ⁻¹ • y)

theorem ksHole_contDiff (δ : ℝ) : ContDiff ℝ ∞ (ksHole δ) :=
  contDiff_const.sub (ksCutoffBase.contDiff.comp (contDiff_const_smul δ⁻¹))

theorem ksHole_nonneg (δ : ℝ) (y : KSSpace) : 0 ≤ ksHole δ y := by
  exact sub_nonneg.mpr ksCutoffBase.le_one

theorem ksHole_le_one (δ : ℝ) (y : KSSpace) : ksHole δ y ≤ 1 := by
  exact sub_le_self _ ksCutoffBase.nonneg

theorem ksHole_zero_on_inner {δ : ℝ} (hδ : 0 < δ) {y : KSSpace} (hy : ‖y‖ ≤ δ) :
    ksHole δ y=0 := by
  have hh : ksCutoffBase (δ⁻¹ • y)=1 := by
    apply ksCutoffBase.one_of_mem_closedBall
    change dist (δ⁻¹ • y) 0 ≤ (1:ℝ)
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hδ]
    calc δ⁻¹*‖y‖ ≤ δ⁻¹*δ := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hδ.le)
      _ = 1 := inv_mul_cancel₀ hδ.ne'
  exact sub_eq_zero.mpr hh.symm

theorem ksHole_one_on_outer {δ : ℝ} (hδ : 0 < δ) {y : KSSpace} (hy : 2*δ ≤ ‖y‖) :
    ksHole δ y=1 := by
  have hh : ksCutoffBase (δ⁻¹ • y)=0 := by
    apply ksCutoffBase.zero_of_le_dist
    change (2:ℝ) ≤ dist (δ⁻¹ • y) 0
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hδ]
    calc (2:ℝ)=δ⁻¹*(2*δ) := by field_simp
      _ ≤ δ⁻¹*‖y‖ := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hδ.le)
  simp only [ksHole,hh,sub_zero]

theorem ksHole_test_tsupport_away {N : ℕ} (i : Fin N) {δ : ℝ} (hδ : 0 < δ)
    (φ : NuclearKSSpace i → ℝ) :
    tsupport (fun q => ksHole δ q.1*φ q) ⊆ {q | δ ≤ ‖q.1‖} := by
  apply closure_minimal _ (isClosed_le continuous_const (continuous_fst.norm))
  intro q hq
  by_contra hn
  have hz := ksHole_zero_on_inner hδ (lt_of_not_ge hn).le
  exact hq (by simp only [hz,zero_mul])

#print axioms ksHole_contDiff
#print axioms ksHole_zero_on_inner
#print axioms ksHole_one_on_outer
#print axioms ksHole_test_tsupport_away
end TheoremT.Continuum
