import RealPositionSpectatorSliceAnalytic_v1
import HomogeneousSpectatorAnisotropicAnalytic_v1

/-! Real-analytic fixed-spectator slices of the actual polynomial double
series. The complex analyticity premise of the generic slicing theorem
is discharged from the actual homogeneity and coefficient bounds.
Position statements use the actual Euclidean norm and ball. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

theorem homogeneous_spectator_real_slice_analyticOnNhd
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (T : Fin d → ℝ) (hT : S*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Fin 3 → ℝ => homogeneousSpectatorSum A
        (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ))))
      {X : Fin 3 → ℝ | D*‖X‖ < 1} :=
  real_fixed_spectator_slice_analyticOnNhd (homogeneousSpectatorSum A)
    (homogeneous_spectator_sum_analytic_anisotropic A hA hM hD hS hL) T hT

theorem homogeneous_spectator_real_position_slice_analyticOnNhd
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (T : EuclideanSpace ℝ (Fin d)) (hT : S*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Position => homogeneousSpectatorSum A
        (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ))))
      {X : Position | D*‖X‖ < 1} :=
  real_position_fixed_spectator_slice_analyticOnNhd (homogeneousSpectatorSum A) hD hS
    (homogeneous_spectator_sum_analytic_anisotropic A hA hM hD hS hL) T hT

theorem homogeneous_spectator_real_position_slice_analyticOnNhd_ball
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 ≤ S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (T : EuclideanSpace ℝ (Fin d)) (hT : S*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Position => homogeneousSpectatorSum A
        (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ))))
      (Metric.ball (0 : Position) D⁻¹) :=
  real_position_fixed_spectator_slice_analyticOnNhd_ball (homogeneousSpectatorSum A) hD hS
    (homogeneous_spectator_sum_analytic_anisotropic A hA hM hD.le hS hL) T hT

end TheoremT.Continuum
