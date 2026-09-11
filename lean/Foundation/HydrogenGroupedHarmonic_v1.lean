import HydrogenSpherePolynomialSpan_v1
import HydrogenPolynomialCalculus_v1
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! A finite harmonic representation grouped by homogeneous degree.
Unlike membership in an abstract span, this supplies one harmonic polynomial
per degree and an actual finite sum on the radius-one Euclidean sphere. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace TheoremT.HydrogenPolynomial

def groupedHarmonicEvaluation : (ℕ →₀ Polynomial3) →ₗ[ℝ] (UnitSphere3 → ℝ) :=
  Finsupp.lsum ℝ (fun _ : ℕ => spherePolynomialEvaluation)

def isGroupedHarmonic (H : ℕ →₀ Polynomial3) : Prop :=
  ∀ m : ℕ, (H m).IsHomogeneous m ∧ polynomialLaplace (H m) = 0

theorem isGroupedHarmonic_zero : isGroupedHarmonic 0 := by
  intro m
  exact ⟨(homogeneousSubmodule (Fin 3) ℝ m).zero_mem, polynomialLaplace_zero⟩

theorem isGroupedHarmonic_add {H K : ℕ →₀ Polynomial3}
    (hH : isGroupedHarmonic H) (hK : isGroupedHarmonic K) : isGroupedHarmonic (H + K) := by
  intro m
  refine ⟨(hH m).1.add (hK m).1, ?_⟩
  simp only [Finsupp.add_apply, polynomialLaplace_add, (hH m).2, (hK m).2, add_zero]

theorem isGroupedHarmonic_smul {H : ℕ →₀ Polynomial3}
    (hH : isGroupedHarmonic H) (c : ℝ) : isGroupedHarmonic (c • H) := by
  intro m
  refine ⟨(homogeneousSubmodule (Fin 3) ℝ m).smul_mem c (hH m).1, ?_⟩
  simp only [Finsupp.smul_apply, polynomialLaplace_smul, (hH m).2, smul_zero]

theorem isGroupedHarmonic_single {m : ℕ} {P : Polynomial3}
    (hP : P.IsHomogeneous m) (hL : polynomialLaplace P = 0) :
    isGroupedHarmonic (Finsupp.single m P) := by
  intro k
  by_cases hk : k = m
  · subst k
    simpa using And.intro hP hL
  · simp only [Finsupp.single_eq_of_ne hk]
    exact ⟨(homogeneousSubmodule (Fin 3) ℝ k).zero_mem, polynomialLaplace_zero⟩

theorem harmonicSphereSpan_has_grouped_representation {f : UnitSphere3 → ℝ}
    (hf : f ∈ harmonicSphereSpan) :
    ∃ H : ℕ →₀ Polynomial3, isGroupedHarmonic H ∧ groupedHarmonicEvaluation H = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, P, hP, hL, rfl⟩ := hf
    refine ⟨Finsupp.single m P, isGroupedHarmonic_single hP hL, ?_⟩
    exact Finsupp.lsum_single _ _ _ _
  | zero => exact ⟨0, isGroupedHarmonic_zero, map_zero _⟩
  | add f g _ _ hf hg =>
    obtain ⟨H, hH, heH⟩ := hf
    obtain ⟨K, hK, heK⟩ := hg
    exact ⟨H + K, isGroupedHarmonic_add hH hK, by rw [map_add, heH, heK]⟩
  | smul c f _ hf =>
    obtain ⟨H, hH, heH⟩ := hf
    exact ⟨c • H, isGroupedHarmonic_smul hH c, by rw [map_smul, heH]⟩

theorem polynomial_has_grouped_sphere_representation (P : Polynomial3) :
    ∃ (s : Finset ℕ) (H : ℕ → Polynomial3),
      (∀ m ∈ s, (H m).IsHomogeneous m ∧ polynomialLaplace (H m) = 0) ∧
      (∀ x : UnitSphere3, spherePolynomialEvaluation P x =
        ∑ m ∈ s, spherePolynomialEvaluation (H m) x) := by
  obtain ⟨H, hH, he⟩ := harmonicSphereSpan_has_grouped_representation
    (spherePolynomialEvaluation_mem_harmonicSphereSpan P)
  refine ⟨H.support, H, fun m _ => hH m, ?_⟩
  intro x
  have hx := congrFun he x
  symm
  simpa [groupedHarmonicEvaluation, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply] using hx

end TheoremT.HydrogenPolynomial

#print axioms TheoremT.HydrogenPolynomial.harmonicSphereSpan_has_grouped_representation
#print axioms TheoremT.HydrogenPolynomial.polynomial_has_grouped_sphere_representation
