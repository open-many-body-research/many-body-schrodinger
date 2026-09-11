import HydrogenGroupedHarmonic_v1

/-! Grouped harmonic polynomial sums on the actual Euclidean unit sphere. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.HydrogenPolynomial

def unitSphere3OfEuclidean (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) : UnitSphere3 :=
  ⟨fun i => x i, by simpa only [← EuclideanSpace.real_norm_sq_eq, hx, one_pow]⟩

theorem polynomial_has_grouped_euclidean_sphere_representation (P : Polynomial3) :
    ∃ (s : Finset ℕ) (H : ℕ → Polynomial3),
      (∀ m ∈ s, (H m).IsHomogeneous m ∧ polynomialLaplace (H m) = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 →
        euclideanEvaluation P x = ∑ m ∈ s, euclideanEvaluation (H m) x) := by
  obtain ⟨s, H, hH, he⟩ := polynomial_has_grouped_sphere_representation P
  refine ⟨s, H, hH, ?_⟩
  intro x hx
  exact he (unitSphere3OfEuclidean x hx)

end TheoremT.HydrogenPolynomial

#print axioms TheoremT.HydrogenPolynomial.polynomial_has_grouped_euclidean_sphere_representation
