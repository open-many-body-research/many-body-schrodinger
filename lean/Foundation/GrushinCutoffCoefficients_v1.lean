import GrushinCutoffL2Bound_v1
import ActualL2IntegralCauchy_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem grushinCutoffWeight_nonneg {c : ℝ} (hc : 0 ≤ c)
    (η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ) (p) :
    0 ≤ grushinCutoffWeight c η p := by
  unfold grushinCutoffWeight
  positivity

theorem grushinCutoffWeight_zero_off_support (c : ℝ)
    (η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ) {p}
    (hp : p ∉ tsupport η) : grushinCutoffWeight c η p = 0 := by
  have hy (i : ι) : partialYDirectional η (oscillatorBasis i) p = 0 := by
    change fderiv ℝ η p (oscillatorBasis i,0) = 0
    rw [fderiv_of_notMem_tsupport ℝ hp]
    rfl
  have ht (j : κ) : partialTDirectional η (oscillatorBasis j) p = 0 := by
    change fderiv ℝ η p (0,oscillatorBasis j) = 0
    rw [fderiv_of_notMem_tsupport ℝ hp]
    rfl
  simp only [grushinCutoffWeight,hy,ht,zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero,mul_zero,add_zero]

theorem grushinCutoffWeight_continuous (c : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ} (hη : ContDiff ℝ ∞ η) :
    Continuous (grushinCutoffWeight c η) := by
  unfold grushinCutoffWeight
  exact (continuous_finsetSum _ (fun i _ => (partialYDirectional_contDiff hη _).continuous.pow 2)).add
    ((continuous_const.mul (continuous_fst.norm.pow 2)).mul
      (continuous_finsetSum _ (fun j _ => (partialTDirectional_contDiff hη _).continuous.pow 2)))

theorem grushinCutoffWeight_exists_bound (c : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, grushinCutoffWeight c η p ≤ C := by
  obtain ⟨C,hC⟩ := hcη.exists_bound_of_continuousOn (grushinCutoffWeight_continuous c hη).continuousOn
  refine ⟨max C 0,le_max_right _ _,fun p => ?_⟩
  by_cases hp : p ∈ tsupport η
  · exact (le_abs_self _).trans ((hC p hp).trans (le_max_left _ _))
  · rw [grushinCutoffWeight_zero_off_support c η hp]
    exact le_max_right _ _

theorem grushinCutoffWeight_explicit_bound {c : ℝ} (hc : 0 ≤ c)
    (A B R : ℝ) (η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ)
    (hY : ∀ p, (∑ i : ι, (partialYDirectional η (oscillatorBasis i) p)^2) ≤ A^2)
    (hT : ∀ p, (∑ j : κ, (partialTDirectional η (oscillatorBasis j) p)^2) ≤ B^2)
    (hR : ∀ p ∈ tsupport η, ‖p.1‖ ≤ R) :
    ∀ p, grushinCutoffWeight c η p ≤ A^2+c*R^2*B^2 := by
  intro p
  by_cases hp : p ∈ tsupport η
  · have hR2 := pow_le_pow_left₀ (norm_nonneg p.1) (hR p hp) 2
    have ht := mul_le_mul_of_nonneg_left (hT p) (mul_nonneg hc (sq_nonneg ‖p.1‖))
    have hr := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR2 hc) (sq_nonneg B)
    exact add_le_add (hY p) (ht.trans hr)
  · rw [grushinCutoffWeight_zero_off_support c η hp]
    positivity

theorem grushin_cutoff_energy_norm_sq_bound (c C : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hb : ∀ p, grushinCutoffWeight c η p ≤ C)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ))) :
    grushinCutoffEnergy c η f ≤ C*‖f‖^2 := by
  have he : ‖f‖^2 = ∫ p, ‖f p‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [he]
  exact grushin_cutoff_energy_l2_bound c C hη hcη hb f

theorem grushin_cutoff_energy_uniform_l2_bound (c : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)),
      grushinCutoffEnergy c η f ≤ C*‖f‖^2 := by
  obtain ⟨C,hC,hb⟩ := grushinCutoffWeight_exists_bound c hη hcη
  exact ⟨C,hC,grushin_cutoff_energy_norm_sq_bound c C hη hcη hb⟩

#print axioms grushinCutoffWeight_exists_bound
#print axioms grushinCutoffWeight_explicit_bound
#print axioms grushin_cutoff_energy_uniform_l2_bound
end TheoremT.Continuum
