import RealFixedSpectatorSliceAnalytic_v1
import ContinuumFoundation_v1

/-! The fixed-spectator analytic slice on the actual physical Position
space, with its Euclidean norm. Spectators use EuclideanSpace in d real
coordinates, hence are also Position when d=3. Coordinate projection
norms are bounded by the Euclidean norm; these norms are not identified
with the finite Pi supremum norm of the complex analytic input. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem complex_coordinates_norm_le_euclidean {ι : Type*} [Fintype ι]
    (X : EuclideanSpace ℝ ι) : ‖fun i => (X i : ℂ)‖ ≤ ‖X‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr
  intro i
  simpa only [Complex.norm_real] using PiLp.norm_apply_le X i

theorem real_position_fixed_spectator_slice_analyticAt {d : ℕ}
    (F : (Fin 3 ⊕ Fin d → ℂ) → ℂ) (T : EuclideanSpace ℝ (Fin d)) (X : Position)
    (hF : AnalyticAt ℂ F (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ)))) :
    AnalyticAt ℝ
      (fun Y : Position => F (Sum.elim (fun i => (Y i : ℂ)) (fun i => (T i : ℂ)))) X := by
  have hmap : AnalyticAt ℝ
      (fun Y : Position => Sum.elim (fun i => (Y i : ℂ)) (fun i => (T i : ℂ))) X := by
    apply AnalyticAt.pi
    intro i
    cases i with
    | inl i =>
      exact (Complex.ofRealCLM.comp
        (EuclideanSpace.proj i : Position →L[ℝ] ℝ)).analyticAt X
    | inr i => exact analyticAt_const
  exact AnalyticAt.comp_of_eq (g := F) (hF.restrictScalars (𝕜 := ℝ)) hmap rfl

theorem real_position_fixed_spectator_slice_analyticOnNhd {d : ℕ}
    (F : (Fin 3 ⊕ Fin d → ℂ) → ℂ) {D S : ℝ} (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hF : AnalyticOnNhd ℂ F {z : Fin 3 ⊕ Fin d → ℂ |
      D*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧ S*‖fun i : Fin d => z (.inr i)‖ < 1})
    (T : EuclideanSpace ℝ (Fin d)) (hT : S*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Position => F (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ))))
      {X : Position | D*‖X‖ < 1} := by
  intro X hX
  change D*‖X‖ < 1 at hX
  apply real_position_fixed_spectator_slice_analyticAt F T X
  apply hF
  constructor
  · change D*‖fun i : Fin 3 => (X i : ℂ)‖ < 1
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (complex_coordinates_norm_le_euclidean X) hD) hX
  · change S*‖fun i : Fin d => (T i : ℂ)‖ < 1
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (complex_coordinates_norm_le_euclidean T) hS) hT

theorem real_position_fixed_spectator_slice_analyticOnNhd_ball {d : ℕ}
    (F : (Fin 3 ⊕ Fin d → ℂ) → ℂ) {D S : ℝ} (hD : 0 < D) (hS : 0 ≤ S)
    (hF : AnalyticOnNhd ℂ F {z : Fin 3 ⊕ Fin d → ℂ |
      D*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧ S*‖fun i : Fin d => z (.inr i)‖ < 1})
    (T : EuclideanSpace ℝ (Fin d)) (hT : S*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Position => F (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ))))
      (Metric.ball (0 : Position) D⁻¹) := by
  apply (real_position_fixed_spectator_slice_analyticOnNhd F hD.le hS hF T hT).mono
  intro X hX
  have hn : ‖X‖ < D⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right] using hX
  change D*‖X‖ < 1
  calc
    _ < D*D⁻¹ := mul_lt_mul_of_pos_left hn hD
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hD)

end TheoremT.Continuum
