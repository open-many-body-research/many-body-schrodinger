import PhysicalKSAnalyticAxisSlice_v1
import PhysicalKSBoxInvariantAnalyticDescentData_v1
import PhysicalRealAxisSliceBounds_v1
import PhysicalAxisRotation_v1
import SO2PolynomialRealRotation_v1
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Real SO(2) invariance of the actual complex A/B axis restrictions.
The radius uses the actual Euclidean physical neighborhood, with the
necessary sqrt(3) comparison to the coordinate sup norm. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSAxisSymmetryRadius (M A : ℝ) : ℝ :=
  min (physicalKSPhysicalSpatialRadius M A / Real.sqrt 3)
    (physicalKSPhysicalSpectatorRadius M A)

theorem physicalKSAxisSymmetryRadius_pos {M A : ℝ} (hA : 1 ≤ A) :
    0 < physicalKSAxisSymmetryRadius M A := by
  exact lt_min (div_pos (physicalKSPhysicalSpatialRadius_pos hA)
    (Real.sqrt_pos.mpr (by norm_num))) (physicalKSPhysicalSpectatorRadius_pos hA)

theorem physicalKSAnalyticDescent_axis_angle_invariant
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {c M A F0 W : ℝ}
    (hdata : PhysicalKSBoxInvariantAnalyticDescentDerivativeData
      f v (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (θ : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hz : ‖z‖ < physicalKSAxisSymmetryRadius M A) :
    physicalKSAnalyticDescentA f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap
          ((fun i => (so2RealRotation (Real.cos θ) (Real.sin θ) z.1 i : ℂ)),
            (fun i => (z.2 i : ℂ)))) =
      physicalKSAnalyticDescentA f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap ((fun i => (z.1 i : ℂ)),(fun i => (z.2 i : ℂ)))) ∧
    physicalKSAnalyticDescentB f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap
          ((fun i => (so2RealRotation (Real.cos θ) (Real.sin θ) z.1 i : ℂ)),
            (fun i => (z.2 i : ℂ)))) =
      physicalKSAnalyticDescentB f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap ((fun i => (z.1 i : ℂ)),(fun i => (z.2 i : ℂ)))) := by
  let q : Fin 4 → ℝ := ![z.1 0,z.1 1,z.2 0,z.2 1]
  have hq : ‖q‖ ≤ ‖z‖ := by
    have hf : ‖z.1‖ ≤ ‖z‖ := le_max_left _ _
    have hs : ‖z.2‖ ≤ ‖z‖ := le_max_right _ _
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    fin_cases i
    · exact (norm_le_pi_norm z.1 0).trans hf
    · exact (norm_le_pi_norm z.1 1).trans hf
    · exact (norm_le_pi_norm z.2 0).trans hs
    · exact (norm_le_pi_norm z.2 1).trans hs
  have hd := physicalRealAxis_domain_of_norm_lt (hq.trans_lt hz)
  have hfix : physicalAxisRotation θ
      ((WithLp.toLp 2 ![0,0,c]) + physicalRealAxisSpectator q) =
      (WithLp.toLp 2 ![0,0,c]) + physicalRealAxisSpectator q := by
    rw [map_add,physicalAxisRotation_axis]
    congr 1
    exact physicalAxisRotation_axis θ (q 3)
  have h := hdata.2 (physicalAxisRotation θ) (physicalRealAxisSpectator q)
    hd.2 hfix (physicalRealAxisSpatial q) hd.1
  have hleft :
      Sum.elim (fun i => (physicalAxisRotation θ (physicalRealAxisSpatial q) i : ℂ))
        (fun i => (physicalRealAxisSpectator q i : ℂ)) =
      physicalKSComplexAxisMap
        ((fun i => (so2RealRotation (Real.cos θ) (Real.sin θ) z.1 i : ℂ)),
          (fun i => (z.2 i : ℂ))) := by
    funext i
    cases i with
    | inl j => fin_cases j <;> simp [physicalAxisRotation_apply,physicalRealAxisSpatial,
        q,physicalKSComplexAxisMap,physicalComplexAxisSlice,so2RealRotation]
    | inr j => fin_cases j <;> simp [physicalRealAxisSpectator,
        q,physicalKSComplexAxisMap,physicalComplexAxisSlice]
  have hright :
      Sum.elim (fun i => (physicalRealAxisSpatial q i : ℂ))
        (fun i => (physicalRealAxisSpectator q i : ℂ)) =
      physicalKSComplexAxisMap ((fun i => (z.1 i : ℂ)),(fun i => (z.2 i : ℂ))) := by
    funext i
    cases i with
    | inl j => fin_cases j <;> simp [physicalRealAxisSpatial,
        q,physicalKSComplexAxisMap,physicalComplexAxisSlice]
    | inr j => fin_cases j <;> simp [physicalRealAxisSpectator,
        q,physicalKSComplexAxisMap,physicalComplexAxisSlice]
  simpa only [hleft,hright] using h

theorem real_unit_pair_exists_angle {a b : ℝ} (hab : a^2+b^2=1) :
    ∃ θ : ℝ, Real.cos θ=a ∧ Real.sin θ=b := by
  let u : ℂ := ⟨a,b⟩
  have hu : ‖u‖=1 := by
    have hs := Complex.normSq_eq_norm_sq u
    have hn := norm_nonneg u
    simp only [Complex.normSq_apply,show u.re=a from rfl,show u.im=b from rfl] at hs
    nlinarith
  have hne : u ≠ 0 := by
    intro he
    simpa [he] using hu
  refine ⟨u.arg,?_,?_⟩
  · simpa only [Complex.cos_arg hne,hu,div_one] using (show u.re=a from rfl)
  · simpa only [Complex.sin_arg,hu,div_one] using (show u.im=b from rfl)

theorem physicalKSAnalyticDescent_axis_rotation_invariant
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {c M A F0 W : ℝ}
    (hdata : PhysicalKSBoxInvariantAnalyticDescentDerivativeData
      f v (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (a b : ℝ) (hab : a^2+b^2=1) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hz : ‖z‖ < physicalKSAxisSymmetryRadius M A) :
    physicalKSAnalyticDescentA f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap ((fun i => (so2RealRotation a b z.1 i : ℂ)),(fun i => (z.2 i : ℂ)))) =
      physicalKSAnalyticDescentA f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap ((fun i => (z.1 i : ℂ)),(fun i => (z.2 i : ℂ)))) ∧
    physicalKSAnalyticDescentB f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap ((fun i => (so2RealRotation a b z.1 i : ℂ)),(fun i => (z.2 i : ℂ)))) =
      physicalKSAnalyticDescentB f (WithLp.toLp 2 ![0,0,c])
        (physicalKSComplexAxisMap ((fun i => (z.1 i : ℂ)),(fun i => (z.2 i : ℂ)))) := by
  obtain ⟨θ,ha,hb⟩ := real_unit_pair_exists_angle hab
  simpa only [ha,hb] using physicalKSAnalyticDescent_axis_angle_invariant hdata θ z hz

end TheoremT.Continuum
