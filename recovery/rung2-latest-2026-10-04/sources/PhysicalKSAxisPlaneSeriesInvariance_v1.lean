import SO2SpectatorSeriesInvariance_v1
import PhysicalKSAxisPlaneSeriesData_v1
import PhysicalKSAnalyticAxisRotation_v1

/-! Local symmetry of the actual physical axis functions implies balanced
support of their actual extracted plane polynomials. Joint real coordinates
are mapped literally to the real and complex product coordinates used by
the existing physical sum and rotation theorems. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def so2JointRealProduct (z : Fin 2 ⊕ Fin 2 → ℝ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  ((fun i => z (Sum.inl i)),(fun i => z (Sum.inr i)))

def so2JointComplexProduct (z : Fin 2 ⊕ Fin 2 → ℝ) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  ((fun i => (z (Sum.inl i) : ℂ)),(fun i => (z (Sum.inr i) : ℂ)))

theorem so2JointRealProduct_norm_le (z : Fin 2 ⊕ Fin 2 → ℝ) :
    ‖so2JointRealProduct z‖ ≤ ‖z‖ := by
  change max ‖fun i : Fin 2 => z (Sum.inl i)‖ ‖fun i : Fin 2 => z (Sum.inr i)‖ ≤ ‖z‖
  apply max_le
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr (fun i => norm_le_pi_norm z (Sum.inl i))
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr (fun i => norm_le_pi_norm z (Sum.inr i))

theorem so2JointComplexProduct_norm_le (z : Fin 2 ⊕ Fin 2 → ℝ) :
    ‖so2JointComplexProduct z‖ ≤ ‖z‖ := by
  change max ‖fun i : Fin 2 => (z (Sum.inl i) : ℂ)‖
    ‖fun i : Fin 2 => (z (Sum.inr i) : ℂ)‖ ≤ ‖z‖
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    simpa only [Complex.norm_real] using norm_le_pi_norm z (Sum.inl i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    simpa only [Complex.norm_real] using norm_le_pi_norm z (Sum.inr i)

theorem so2JointComplexProduct_elim (z : Fin 2 ⊕ Fin 2 → ℝ) :
    Sum.elim (so2JointComplexProduct z).1 (so2JointComplexProduct z).2 =
      (fun i => (z i : ℂ)) := by
  funext i
  cases i <;> rfl

theorem so2JointComplexProduct_rotation (a b : ℝ) (z : Fin 2 ⊕ Fin 2 → ℝ) :
    so2JointComplexProduct (so2JointRealRotationCLM a b z) =
      ((fun i => (so2RealRotation a b (so2JointRealProduct z).1 i : ℂ)),
        (fun i => ((so2JointRealProduct z).2 i : ℂ))) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem physicalKSAxisPlanePolynomial_balanced_support
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ} {c M A F0 W : ℝ}
    (hq : PhysicalKSAxisPolynomialData f (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hdata : PhysicalKSBoxInvariantAnalyticDescentDerivativeData
      f v (WithLp.toLp 2 ![0,0,c]) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    (∀ j γ d, d ∈ (so2PolynomialToBalanced
      (physicalKSAxisPlanePolynomialA f (WithLp.toLp 2 ![0,0,c]) j γ)).support → d 0=d 1) ∧
    (∀ j γ d, d ∈ (so2PolynomialToBalanced
      (physicalKSAxisPlanePolynomialB f (WithLp.toLp 2 ![0,0,c]) j γ)).support → d 0=d 1) := by
  obtain ⟨hqa,hqb,hla,hlb,hsa,hsb⟩ := hq
  have hB := physicalKSAxisSeriesRate_pos (M := M) hA
  have hp := physicalKSPointwiseAmplitude_nonneg (M := M) (W := W) hA hF0
  have hd : 0 ≤ 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  let fa : (Fin 2 ⊕ Fin 2 → ℝ) → ℂ := fun z =>
    physicalKSAnalyticDescentA f (WithLp.toLp 2 ![0,0,c])
      (physicalKSComplexAxisMap (so2JointComplexProduct z))
  let fb : (Fin 2 ⊕ Fin 2 → ℝ) → ℂ := fun z =>
    physicalKSAnalyticDescentB f (WithLp.toLp 2 ![0,0,c])
      (physicalKSComplexAxisMap (so2JointComplexProduct z))
  have he : ∀ᶠ z in 𝓝 (0 : Fin 2 ⊕ Fin 2 → ℝ),
      physicalKSAxisSeriesRate M A*‖so2JointComplexProduct z‖<1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Fin 2 ⊕ Fin 2 → ℝ) (inv_pos.mpr hB)] with z hz
    have hz' : ‖z‖ < (physicalKSAxisSeriesRate M A)⁻¹ := by simpa using hz
    calc
      _ ≤ physicalKSAxisSeriesRate M A*‖z‖ :=
        mul_le_mul_of_nonneg_left (so2JointComplexProduct_norm_le z) hB.le
      _ < physicalKSAxisSeriesRate M A*(physicalKSAxisSeriesRate M A)⁻¹ :=
        mul_lt_mul_of_pos_left hz' hB
      _ = 1 := mul_inv_cancel₀ hB.ne'
  have hsa' : ∀ᶠ z in 𝓝 0,
      HasSum (fun n => eval (fun i => (z i : ℂ))
        (physicalKSAxisPolynomialA f (WithLp.toLp 2 ![0,0,c]) n)) (fa z) := by
    filter_upwards [he] with z hz
    simpa only [so2JointComplexProduct_elim,fa,physicalKSComplexAxisMap_apply] using hsa _ hz
  have hsb' : ∀ᶠ z in 𝓝 0,
      HasSum (fun n => eval (fun i => (z i : ℂ))
        (physicalKSAxisPolynomialB f (WithLp.toLp 2 ![0,0,c]) n)) (fb z) := by
    filter_upwards [he] with z hz
    simpa only [so2JointComplexProduct_elim,fb,physicalKSComplexAxisMap_apply] using hsb _ hz
  have hi (a b : ℝ) (hab : a^2+b^2=1) :
      (fa ∘ so2JointRealRotationCLM a b) =ᶠ[𝓝 0] fa ∧
      (fb ∘ so2JointRealRotationCLM a b) =ᶠ[𝓝 0] fb := by
    have hh : ∀ᶠ z in 𝓝 (0 : Fin 2 ⊕ Fin 2 → ℝ),
        fa (so2JointRealRotationCLM a b z)=fa z ∧
        fb (so2JointRealRotationCLM a b z)=fb z := by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin 2 ⊕ Fin 2 → ℝ)
        (physicalKSAxisSymmetryRadius_pos hA)] with z hz
      have hz' : ‖z‖ < physicalKSAxisSymmetryRadius M A := by simpa using hz
      have hr := physicalKSAnalyticDescent_axis_rotation_invariant hdata a b hab
        (so2JointRealProduct z) ((so2JointRealProduct_norm_le z).trans_lt hz')
      dsimp only [fa,fb]
      rw [so2JointComplexProduct_rotation]
      exact hr
    exact ⟨hh.mono (fun _ h => h.1),hh.mono (fun _ h => h.2)⟩
  constructor
  · exact so2SpectatorFamily_balanced_support_of_hasSum _ hqa
      (mul_nonneg (by norm_num) hp) hB.le hla fa hsa' (fun a b hab => (hi a b hab).1)
  · exact so2SpectatorFamily_balanced_support_of_hasSum _ hqb
      (mul_nonneg (by norm_num) (mul_nonneg hp hd)) hB.le hlb fb hsb'
      (fun a b hab => (hi a b hab).2)

end TheoremT.Continuum
