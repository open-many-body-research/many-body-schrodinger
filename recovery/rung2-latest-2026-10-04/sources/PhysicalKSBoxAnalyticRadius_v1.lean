import CoulombKSPhysicalPointwise_v1

/-! A center-independent radius for the literal derivative power series of
the physical KS base, valid on a smaller closed rectangle. The Euclidean
block norms and their maximum product norm are used without identifying
rectangles with balls. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ContDiff NNReal ENNReal
namespace TheoremT.Continuum
open WeakGrushin

theorem physical_boxCoordinate_abs_le_norm (i : Fin 4 ⊕ Fin 3) (p : Space (Fin 3)) :
    |boxCoordinate i p| ≤ ‖p‖ := by
  cases i with
  | inl j =>
    exact (PiLp.norm_apply_le p.1 j).trans (norm_fst_le p)
  | inr j =>
    exact (PiLp.norm_apply_le p.2 j).trans (norm_snd_le p)

theorem physical_fixed_box_ball_room (z x : Space (Fin 3))
    (hx : x ∈ rectangularClosedBox z (1/1024) (1/1024)) :
    Metric.ball x (1/1024) ⊆ rectangularOpenBox z (1/512) (1/512) := by
  intro p hp i
  have hp' : ‖p-x‖ < (1/1024 : ℝ) := by simpa only [Metric.mem_ball,dist_eq_norm] using hp
  have hx' : |boxCoordinate i (x-z)| ≤ (1/1024 : ℝ) := by
    have h := hx i
    cases i <;> exact h
  have hh : |boxCoordinate i (p-z)| < (1/512 : ℝ) := by
    have he : p-z = (p-x)+(x-z) := by abel
    rw [he,map_add]
    have hcoord := physical_boxCoordinate_abs_le_norm i (p-x)
    have htri := abs_add_le (boxCoordinate i (p-x)) (boxCoordinate i (x-z))
    linarith
  cases i <;> exact hh

theorem physicalKSBoxPointwiseData_common_radius
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1 ≤ A) (hF0 : 0 ≤ F0) :
    ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ) = min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹ ∧
      ∀ x ∈ rectangularClosedBox (0,t0) (1/1024) (1/1024),
        HasFPowerSeriesOnBall f (factorialFrechetSeries f x) x (r : ℝ≥0∞) := by
  exact physical_coordinate_factorial_common_radius (rectangularOpenBox_isOpen (0,t0) _ _)
    hdata.1 (physicalKSPointwiseAmplitude_nonneg hA hF0)
    (physicalKSPointwiseRate_pos hA) (by norm_num : (0 : ℝ) < 1/1024)
    (fun x hx w => hdata.2.2 w x hx)
    (fun x hx => physical_fixed_box_ball_room (0,t0) x hx)

end TheoremT.Continuum
