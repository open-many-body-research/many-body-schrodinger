import PhysicalKSAnalyticDescentCompatibility_v1
import AnalyticNormIsometryInvariance_v1

/-! Transport a physical slice symmetry to the actual A/B coefficients.
The physical identity and real analyticity remain explicit in the generic
lemma; the nuclear and pair consumers supply both from their pointwise data. -/
noncomputable section
set_option autoImplicit false
open Metric
namespace TheoremT.Continuum
open WeakGrushin

theorem physicalKSPhysicalSpectatorRadius_rate_bound {M A : ℝ} (hA : 1≤A)
    (T : Position) (hT : ‖T‖<physicalKSPhysicalSpectatorRadius M A) :
    (7*physicalKSPointwiseRate M A)*‖T‖<1 := by
  have hS : 0<7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hn := hT.trans_le (min_le_right (1/1024) (7*physicalKSPointwiseRate M A)⁻¹)
  calc
    _ < (7*physicalKSPointwiseRate M A)*(7*physicalKSPointwiseRate M A)⁻¹ :=
      mul_lt_mul_of_pos_left hn hS
    _ = 1 := mul_inv_cancel₀ hS.ne'

theorem physicalKSAnalyticDescent_isometry_invariant_of_slice
    {f : Space (Fin 3) → ℂ} {g : Position → Position → ℂ}
    {t0 : Position} {M A : ℝ} (hA : 1≤A)
    (h0 : PhysicalKSAnalyticDescentOnPhysicalNeighborhood f g t0 M A)
    (T : Position) (hT : ‖T‖<physicalKSPhysicalSpectatorRadius M A)
    (ha : AnalyticOnNhd ℝ (fun X : Position => physicalKSAnalyticDescentA f t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
        (ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹) ∧
      AnalyticOnNhd ℝ (fun X : Position => physicalKSAnalyticDescentB f t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
        (ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹))
    (R : Position ≃ₗᵢ[ℝ] Position)
    (hinv : ∀ X ∈ ball (0 : Position) (physicalKSPhysicalSpatialRadius M A),
      g (R X) (t0+T)=g X (t0+T))
    (X : Position) (hX : ‖X‖<physicalKSPhysicalSpatialRadius M A) :
    physicalKSAnalyticDescentA f t0
        (Sum.elim (fun j => (R X j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentA f t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) ∧
    physicalKSAnalyticDescentB f t0
        (Sum.elim (fun j => (R X j : ℂ)) (fun j => (T j : ℂ))) =
      physicalKSAnalyticDescentB f t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))) := by
  have hsub : ball (0 : Position) (physicalKSPhysicalSpatialRadius M A) ⊆
      ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹ :=
    ball_subset_ball (min_le_right _ _)
  obtain ⟨r,hr,he,hid⟩ := h0
  rw [he] at hid
  have hu := analytic_norm_coefficients_isometry_invariant
    (physicalKSPhysicalSpatialRadius_pos hA) (ha.1.mono hsub) (ha.2.mono hsub)
    (u := fun Y => g Y (t0+T))
    (fun Y hY => by
      have hn : ‖Y‖<physicalKSPhysicalSpatialRadius M A := by
        simpa only [mem_ball,dist_zero_right] using hY
      simpa only [Complex.real_smul] using hid Y T hn hT) R hinv
  have hx : X ∈ ball (0 : Position) (physicalKSPhysicalSpatialRadius M A) := by
    simpa only [mem_ball,dist_zero_right] using hX
  exact ⟨hu.1 hx,hu.2 hx⟩

end TheoremT.Continuum
