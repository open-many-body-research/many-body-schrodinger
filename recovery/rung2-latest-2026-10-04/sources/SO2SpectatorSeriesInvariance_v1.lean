import HomogeneousPolynomialSeriesRealUniqueness_v1
import SO2SpectatorCoefficientInvariance_v1
import SO2SpectatorFamilySeries_v1

/-! Local real planar symmetry of the actual convergent joint series
forces symmetry and balanced support of the actual extracted family.
Neither polynomial symmetry nor coefficient symmetry is a premise. -/
noncomputable section
set_option autoImplicit false
open scoped Topology BigOperators
namespace TheoremT.Continuum
open MvPolynomial

theorem so2SpectatorFamily_rotation_invariant_of_hasSum
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) {C B : ℝ} (hC : 0≤C) (hB : 0≤B)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (F : (Fin 2 ⊕ Fin 2 → ℝ) → ℂ)
    (hsum : ∀ᶠ z in 𝓝 0,
      HasSum (fun n => eval (fun i => (z i : ℂ)) (Q n)) (F z))
    (a b : ℝ) (hi : (F ∘ so2JointRealRotationCLM a b) =ᶠ[𝓝 0] F)
    (j : ℕ) (γ : Fin 2 → ℕ) (y : Fin 2 → ℝ) :
    eval (fun i => (so2RealRotation a b y i : ℂ)) (so2SpectatorFamily Q j γ) =
      eval (fun i => (y i : ℂ)) (so2SpectatorFamily Q j γ) := by
  apply so2SpectatorCoefficientPolynomial_rotation_invariant
  intro z
  exact homogeneous_polynomial_series_real_linear_invariant_of_hasSum
    Q hQ hC hB hL F (so2JointRealRotationCLM a b) hsum hi _ z

theorem so2SpectatorFamily_balanced_support_of_hasSum
    (Q : ℕ → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (hQ : ∀ n, (Q n).IsHomogeneous n) {C B : ℝ} (hC : 0≤C) (hB : 0≤B)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (F : (Fin 2 ⊕ Fin 2 → ℝ) → ℂ)
    (hsum : ∀ᶠ z in 𝓝 0,
      HasSum (fun n => eval (fun i => (z i : ℂ)) (Q n)) (F z))
    (hi : ∀ a b : ℝ, a^2+b^2=1 → (F ∘ so2JointRealRotationCLM a b) =ᶠ[𝓝 0] F)
    (j : ℕ) (γ : Fin 2 → ℕ) :
    ∀ d ∈ (so2PolynomialToBalanced (so2SpectatorFamily Q j γ)).support, d 0=d 1 := by
  apply so2PolynomialToBalanced_balanced_support_of_real_rotation
  intro a b hab y
  exact so2SpectatorFamily_rotation_invariant_of_hasSum Q hQ hC hB hL F hsum
    a b (hi a b hab) j γ y

end TheoremT.Continuum
