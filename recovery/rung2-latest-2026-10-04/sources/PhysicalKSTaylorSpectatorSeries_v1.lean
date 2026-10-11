import PhysicalKSTaylorSpectatorCoefficients_v1
import HomogeneousSpectatorFiniteVariables_v1

/-! Absolute convergence of the actual extracted KS Taylor coefficients,
indexed by the Y degree and the literal spectator multiindex. This is the
original four-variable series before selecting even Y degree or descending. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def physicalKSTaylorSpectatorFamily (f : Space (Fin 3) → ℂ)
    (x : Space (Fin 3)) (j : ℕ) (γ : Fin 3 → ℕ) : MvPolynomial (Fin 4) ℂ :=
  physicalKSTaylorSpectatorCoefficient f x j (Finsupp.equivFunOnFinite.symm γ)

theorem physicalKSTaylorSpectatorFamily_homogeneous
    (f : Space (Fin 3) → ℂ) (x : Space (Fin 3)) (j : ℕ) (γ : Fin 3 → ℕ) :
    (physicalKSTaylorSpectatorFamily f x j γ).IsHomogeneous j :=
  physicalKSTaylorSpectatorCoefficient_homogeneous f x j _

theorem physicalKSTaylorSpectatorFamily_coefficientL1
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {x : Space (Fin 3)}
    (hx : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512))
    (j : ℕ) (γ : Fin 3 → ℕ) :
    polynomialCoeffL1 (physicalKSTaylorSpectatorFamily f x j γ) ≤
      physicalKSPointwiseAmplitude M A F0 W *
        (7*physicalKSPointwiseRate M A)^j *
        (7*physicalKSPointwiseRate M A)^(∑ i : Fin 3, γ i) := by
  have h := physicalKSTaylorSpectatorCoefficient_coefficientL1 hdata hA hF0 hx j
    (Finsupp.equivFunOnFinite.symm γ)
  simpa [physicalKSTaylorSpectatorFamily,Finsupp.degree_eq_sum,pow_add,mul_assoc] using h

theorem physicalKSTaylorSpectatorFamily_summable
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {x : Space (Fin 3)}
    (hx : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512))
    (y : Fin 4 → ℂ) (t : Fin 3 → ℂ)
    (hy : (7*physicalKSPointwiseRate M A)*‖y‖<1)
    (ht : (7*physicalKSPointwiseRate M A)*‖t‖<1) :
    Summable (fun k : ℕ × (Fin 3 → ℕ) =>
      ‖eval y (physicalKSTaylorSpectatorFamily f x k.1 k.2) * ∏ i : Fin 3, t i ^ k.2 i‖) ∧
    Summable (fun k : ℕ × (Fin 3 → ℕ) =>
      eval y (physicalKSTaylorSpectatorFamily f x k.1 k.2) * ∏ i : Fin 3, t i ^ k.2 i) := by
  have hS : 0 ≤ 7*physicalKSPointwiseRate M A :=
    mul_nonneg (by norm_num) (physicalKSPointwiseRate_pos hA).le
  exact homogeneous_spectator_finite_variables_summable _
    (physicalKSTaylorSpectatorFamily_homogeneous f x)
    (physicalKSPointwiseAmplitude_nonneg hA hF0) hS (norm_nonneg y) hS (norm_nonneg t)
    hy ht (physicalKSTaylorSpectatorFamily_coefficientL1 hdata hA hF0 hx) y t
    (fun i => norm_le_pi_norm y i) (fun i => norm_le_pi_norm t i)

end TheoremT.Continuum
