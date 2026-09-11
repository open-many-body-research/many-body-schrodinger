import HydrogenWeakDerivatives_v1
import HydrogenRadialTrace_v1

/-! The actual one-electron Coulomb graph contains the explicit nonzero
hydrogen radial eigenfunction. The physical operator, weak H2 domain, and
kinetic factor one half are those of ContinuumFoundation_v1. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

theorem hydrogenRadialL2_eigenGraph (Z : ℝ) (hZ : 0 < Z) :
    scalarHamiltonianGraph 1 Z (hydrogenRadialL2 Z hZ)
      ((-(Z ^ 2 / 2) : ℂ) • hydrogenRadialL2 Z hZ) := by
  refine ⟨hydrogenFirstL2 Z hZ, hydrogenSecondL2 Z hZ,
    hydrogen_first_weakPartial hZ, hydrogen_second_weakPartial hZ, ?_⟩
  have he : ∀ᵐ x : Configuration 1 ∂volume, ∀ k : Coordinate 1,
      hydrogenSecondL2 Z hZ k k x = hydrogenSecond Z k k x := by
    rw [ae_all_iff]
    intro k
    exact (hydrogen_second_memLp hZ k k).coeFn_toLp
  filter_upwards [Lp.coeFn_smul (-(Z ^ 2 / 2) : ℂ) (hydrogenRadialL2 Z hZ),
    hydrogenRadialL2_coe_ae Z hZ, he, hydrogen_ae_ne_zero] with x hout hf he hx
  simp only [Pi.smul_apply, smul_eq_mul] at hout
  rw [hout, hf]
  simp_rw [he]
  rw [hydrogenSecond_trace Z hx, coulombPotential_one_electron Z x]
  push_cast
  ring

/-- An explicit nonzero actual L2 eigenvector, rather than a selected solution
of an existence-only theorem. Its scalar norm is available separately. -/
theorem hydrogen_explicit_scalar_eigenpair (Z : ℝ) (hZ : 0 < Z) :
    hydrogenRadialL2 Z hZ ≠ 0 ∧ HasH2 (hydrogenRadialL2 Z hZ) ∧
      scalarHamiltonianGraph 1 Z (hydrogenRadialL2 Z hZ)
        ((-(Z ^ 2 / 2) : ℂ) • hydrogenRadialL2 Z hZ) :=
  ⟨hydrogenRadialL2_ne_zero Z hZ, hydrogenRadialL2_hasH2 hZ,
    hydrogenRadialL2_eigenGraph Z hZ⟩

#print axioms hydrogenRadialL2_eigenGraph
#print axioms hydrogen_explicit_scalar_eigenpair
end TheoremT.Continuum
