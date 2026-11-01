import PhysicalComplexAxisSlice_v1
import PhysicalKSBoxAnalyticDescentData_v2

/-! A literal four-complex-variable axis restriction of the physical A/B
functions. Its product/Pi norms are coordinate sup norms. The proved
quarter-polydisc derivative estimates at order zero supply explicit bounds;
the physical real Euclidean neighborhood is a separate obligation. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSComplexAxisMap
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : Fin 3 ⊕ Fin 3 → ℂ :=
  physicalComplexAxisSlice ![z.1 0,z.1 1,z.2 0,z.2 1]

def physicalKSComplexAxisMapCLM :
    ((Fin 2 → ℂ) × (Fin 2 → ℂ)) →L[ℂ] (Fin 3 ⊕ Fin 3 → ℂ) :=
  ({ toFun := physicalKSComplexAxisMap
     map_add' := by
       intro x y
       funext j
       cases j with
       | inl i => fin_cases i <;> simp [physicalKSComplexAxisMap,physicalComplexAxisSlice]
       | inr i => fin_cases i <;> simp [physicalKSComplexAxisMap,physicalComplexAxisSlice]
     map_smul' := by
       intro c x
       funext j
       cases j with
       | inl i => fin_cases i <;> simp [physicalKSComplexAxisMap,physicalComplexAxisSlice]
       | inr i => fin_cases i <;> simp [physicalKSComplexAxisMap,physicalComplexAxisSlice] } :
    ((Fin 2 → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin 3 ⊕ Fin 3 → ℂ)).toContinuousLinearMap

theorem physicalKSComplexAxisMap_apply (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    physicalKSComplexAxisMap z = Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1] := rfl

theorem physicalKSComplexAxisMap_block_norms (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    ‖fun i : Fin 3 => physicalKSComplexAxisMap z (.inl i)‖ ≤ ‖z‖ ∧
    ‖fun i : Fin 3 => physicalKSComplexAxisMap z (.inr i)‖ ≤ ‖z‖ := by
  have hf : ‖z.1‖ ≤ ‖z‖ := le_max_left _ _
  have hs : ‖z.2‖ ≤ ‖z‖ := le_max_right _ _
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    fin_cases i
    · simpa [physicalKSComplexAxisMap,physicalComplexAxisSlice] using (norm_le_pi_norm z.1 0).trans hf
    · simpa [physicalKSComplexAxisMap,physicalComplexAxisSlice] using (norm_le_pi_norm z.1 1).trans hf
    · simpa [physicalKSComplexAxisMap,physicalComplexAxisSlice] using (norm_le_pi_norm z.2 0).trans hs
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    fin_cases i
    · simp [physicalKSComplexAxisMap,physicalComplexAxisSlice]
    · simp [physicalKSComplexAxisMap,physicalComplexAxisSlice]
    · simpa [physicalKSComplexAxisMap,physicalComplexAxisSlice] using (norm_le_pi_norm z.2 1).trans hs

def physicalKSAnalyticAxisRadius (M A : ℝ) : ℝ :=
  min (4*(32*(7*physicalKSPointwiseRate M A)^2))⁻¹
    (4*(7*physicalKSPointwiseRate M A))⁻¹

theorem physicalKSAnalyticAxisRadius_pos {M A : ℝ} (hA : 1 ≤ A) :
    0 < physicalKSAnalyticAxisRadius M A := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  dsimp [physicalKSAnalyticAxisRadius]
  positivity

theorem physicalKSComplexAxisMap_quarter_bounds {M A : ℝ} (hA : 1 ≤ A)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : ‖z‖ < physicalKSAnalyticAxisRadius M A) :
    (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => physicalKSComplexAxisMap z (.inl i)‖ ≤ 1/4 ∧
    (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => physicalKSComplexAxisMap z (.inr i)‖ ≤ 1/4 := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0 < 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hsmall (c : ℝ) (hc : 0 < c) (hb : ‖z‖ < (4*c)⁻¹) : c*‖z‖ < 1/4 := by
    have ht : ‖z‖*(4*c) < 1 :=
      (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hc)).mp (by simpa [one_div] using hb)
    nlinarith
  have hb := physicalKSComplexAxisMap_block_norms z
  constructor
  · exact (mul_le_mul_of_nonneg_left hb.1 hD.le).trans
      (hsmall _ hD (hz.trans_le (min_le_left _ _))).le
  · exact (mul_le_mul_of_nonneg_left hb.2 hS.le).trans
      (hsmall _ hS (hz.trans_le (min_le_right _ _))).le

theorem physicalKSAnalyticDescent_axis_analytic_bounded
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxAnalyticDescentDerivativeData f v t0 M A F0 W)
    (hA : 1 ≤ A) :
    AnalyticOnNhd ℂ (fun z => physicalKSAnalyticDescentA f t0 (physicalKSComplexAxisMap z))
      (Metric.ball 0 (physicalKSAnalyticAxisRadius M A)) ∧
    AnalyticOnNhd ℂ (fun z => physicalKSAnalyticDescentB f t0 (physicalKSComplexAxisMap z))
      (Metric.ball 0 (physicalKSAnalyticAxisRadius M A)) ∧
    ∀ z : (Fin 2 → ℂ) × (Fin 2 → ℂ), ‖z‖ < physicalKSAnalyticAxisRadius M A →
      ‖physicalKSAnalyticDescentA f t0 (physicalKSComplexAxisMap z)‖ ≤
        16*physicalKSPointwiseAmplitude M A F0 W ∧
      ‖physicalKSAnalyticDescentB f t0 (physicalKSComplexAxisMap z)‖ ≤
        (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W) := by
  have hdom (z : (Fin 2 → ℂ) × (Fin 2 → ℂ))
      (hz : z ∈ Metric.ball 0 (physicalKSAnalyticAxisRadius M A)) :
      (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => physicalKSComplexAxisMap z (.inl i)‖ < 1 ∧
      (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => physicalKSComplexAxisMap z (.inr i)‖ < 1 := by
    have hb := physicalKSComplexAxisMap_quarter_bounds hA z (by simpa using hz)
    constructor <;> linarith [hb.1,hb.2]
  refine ⟨?_,?_,?_⟩
  · intro z hz
    exact (hdata.1.2.1 _ (hdom z hz)).comp
      (physicalKSComplexAxisMapCLM.analyticAt z)
  · intro z hz
    exact (hdata.1.2.2.1 _ (hdom z hz)).comp
      (physicalKSComplexAxisMapCLM.analyticAt z)
  · intro z hz
    have hb := physicalKSComplexAxisMap_quarter_bounds hA z hz
    have h := hdata.2.1 (physicalKSComplexAxisMap z) hb.1 hb.2 (fun _ => 0) (fun _ => 0)
    have he : Sum.elim (fun _ : Fin 3 => (0 : ℕ)) (fun _ : Fin 3 => 0) =
        (fun _ : Fin 3 ⊕ Fin 3 => 0) := by
      funext i
      cases i <;> rfl
    rw [he] at h
    have hzder (F : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ) (q : Fin 3 ⊕ Fin 3 → ℂ) :
        complexMultiindexDeriv F (fun _ => 0) q = F q := by
      change (iteratedFDeriv ℂ 0 F q) _ = F q
      exact iteratedFDeriv_zero_apply _
    simpa [hzder,physicalKSDescentDerivativeBudget] using h

end TheoremT.Continuum
