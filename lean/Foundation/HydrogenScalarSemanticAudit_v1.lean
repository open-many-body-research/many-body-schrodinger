import HydrogenEigenGraph_v1
import HydrogenRadialNorm_v1

/-! Literal semantic audit: three real spatial coordinates, complex Lebesgue
L2, all compact smooth real tests, all nine ordered second derivatives, and the
unsoftened one-body Coulomb output. Printed proof bodies are omitted only to
make the complete mathematical statement readable. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem audit_explicit_hydrogen_weakH2_eigenpair (Z : ℝ) (hZ : 0 < Z) :
    ∃ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 1 × Fin 3))),
      f ≠ 0 ∧ ‖f‖ ^ 2 = Real.pi / Z ^ 3 ∧
      (∀ᵐ x ∂volume, f x = (Real.exp (-Z * ‖x‖) : ℂ)) ∧
      ∃ d : (Fin 1 × Fin 3) → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 1 × Fin 3))),
      ∃ e : (Fin 1 × Fin 3) → (Fin 1 × Fin 3) →
          Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 1 × Fin 3))),
        (∀ k, ∀ φ : EuclideanSpace ℝ (Fin 1 × Fin 3) → ℝ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ x, φ x • d k x) =
            -(∫ x, fderiv ℝ φ x (PiLp.single 2 k 1) • f x)) ∧
        (∀ k l, ∀ φ : EuclideanSpace ℝ (Fin 1 × Fin 3) → ℝ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ x, φ x • e k l x) =
            -(∫ x, fderiv ℝ φ x (PiLp.single 2 l 1) • d k x)) ∧
        (∀ᵐ x ∂volume,
          (-(Z ^ 2 / 2) : ℂ) * f x =
            (-((1 : ℂ) / 2)) * (∑ k : Fin 1 × Fin 3, e k k x) +
              ((-Z / ‖x‖ : ℝ) : ℂ) * f x) := by
  refine ⟨hydrogenRadialL2 Z hZ, hydrogenRadialL2_ne_zero Z hZ,
    hydrogenRadialL2_norm_sq Z hZ, hydrogenRadialL2_coe_ae Z hZ,
    hydrogenFirstL2 Z hZ, hydrogenSecondL2 Z hZ,
    hydrogen_first_weakPartial hZ, hydrogen_second_weakPartial hZ, ?_⟩
  obtain ⟨d, e, hd, he, hout⟩ := hydrogenRadialL2_eigenGraph Z hZ
  have hdEq : d = hydrogenFirstL2 Z hZ := by
    funext k
    exact weakPartial_unique (hd k) (hydrogen_first_weakPartial hZ k)
  have heEq : e = hydrogenSecondL2 Z hZ := by
    funext k l
    exact weakPartial_unique (by simpa only [hdEq] using he k l)
      (hydrogen_second_weakPartial hZ k l)
  rw [heEq] at hout
  filter_upwards [hout, Lp.coeFn_smul (-(Z ^ 2 / 2) : ℂ) (hydrogenRadialL2 Z hZ)]
    with x hx hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, coulombPotential_one_electron Z x] at hx
  exact hx

set_option pp.proofs false in
#print audit_explicit_hydrogen_weakH2_eigenpair
#print axioms audit_explicit_hydrogen_weakH2_eigenpair
#print axioms hydrogenRadialL2_eigenGraph
#print axioms hydrogenRadialL2_hasH2
#print axioms hydrogenRadialL2_norm_sq
#print axioms weakPartial_of_classical_dominated_limit
end TheoremT.Continuum
