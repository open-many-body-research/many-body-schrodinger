import SO2AxisPolynomialRestriction_v1
import HomogeneousSpectatorSeriesDerivative_v1
import HomogeneousPolynomialGeometricSeries_v1

/-! The actual grouped four-coordinate axis polynomials of a given A/B
family. Their coefficient L1 is inherited by literal substitution, with
only the previously stated binomial-to-geometric grouping loss. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
namespace TheoremT.Continuum

def so2AxisGroupedPolynomial
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ) (n : ℕ) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  so2AxisPolynomialRestriction (groupedHomogeneousSpectatorPolynomial A n)

theorem so2AxisGroupedPolynomial_homogeneous
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) (n : ℕ) :
    (so2AxisGroupedPolynomial A n).IsHomogeneous n :=
  so2AxisPolynomialRestriction_homogeneous (groupedHomogeneousSpectatorPolynomial_isHomogeneous A hA n)

theorem so2AxisGroupedPolynomial_coeffL1
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin 3, γ i)) (n : ℕ) :
    polynomialCoeffL1 (so2AxisGroupedPolynomial A n) ≤ (8*M)*(2*T)^n := by
  apply (so2AxisPolynomialRestriction_coeffL1 _).trans
  have hh := polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial_coarse A hM hT hL n
  convert hh using 1 <;> first | rfl | ring

theorem so2_axis_coordinate_norm_le (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    ‖(Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1] : Fin 3 ⊕ Fin 3 → ℂ)‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · exact (norm_le_pi_norm z.1 0).trans (norm_fst_le z)
    · exact (norm_le_pi_norm z.1 1).trans (norm_fst_le z)
    · exact (norm_le_pi_norm z.2 0).trans (norm_snd_le z)
  | inr i =>
    fin_cases i
    · simpa using norm_nonneg z
    · simpa using norm_nonneg z
    · exact (norm_le_pi_norm z.2 1).trans (norm_snd_le z)

theorem so2AxisGroupedPolynomial_hasSum
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*T^(m+∑ i : Fin 3, γ i))
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : (2*T)*‖z‖ < 1) :
    Summable (fun n => ‖MvPolynomial.eval (Sum.elim z.1 z.2) (so2AxisGroupedPolynomial A n)‖) ∧
    HasSum (fun n => MvPolynomial.eval (Sum.elim z.1 z.2) (so2AxisGroupedPolynomial A n))
      (homogeneousSpectatorSum A (Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1])) := by
  have hzcoords : Sum.elim z.1 z.2 ∈ complexClosedPolydisc (Fin 2 ⊕ Fin 2) ‖z‖ := by
    intro i
    cases i with
    | inl i => exact (norm_le_pi_norm z.1 i).trans (norm_fst_le z)
    | inr i => exact (norm_le_pi_norm z.2 i).trans (norm_snd_le z)
  have habs := homogeneous_polynomial_series_summable_norm (so2AxisGroupedPolynomial A)
    (so2AxisGroupedPolynomial_homogeneous A hA) (by positivity : 0 ≤ 2*T)
    (norm_nonneg z) hz (so2AxisGroupedPolynomial_coeffL1 A hM hT hL) _ hzcoords
  have hsmall : T*‖(Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1] : Fin 3 ⊕ Fin 3 → ℂ)‖ < 1 := by
    have hn := mul_le_mul_of_nonneg_left (so2_axis_coordinate_norm_le z) hT
    nlinarith [mul_nonneg hT (norm_nonneg z)]
  have hval := (homogeneousSpectatorSum_eventuallyEq_grouped A hA hM hT hL
    (Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1]) hsmall).eq_of_nhds
  have heq : (∑' n, MvPolynomial.eval (Sum.elim z.1 z.2) (so2AxisGroupedPolynomial A n)) =
      homogeneousSpectatorSum A (Sum.elim ![z.1 0,z.1 1,z.2 0] ![0,0,z.2 1]) := by
    rw [hval]
    apply tsum_congr
    intro n
    exact so2AxisPolynomialRestriction_eval _ z
  refine ⟨habs, ?_⟩
  rw [← heq]
  exact habs.of_norm.hasSum

end TheoremT.Continuum
