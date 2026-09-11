import CoulombH1Infimum_v1
import CoulombH1IntegralForm_v1

/-! Mathematical statement expansion for the actual H¹ form/energy bridge.
Physical spaces, every first-weak-derivative test, spin permutations and the
untruncated potential are displayed. Normed-space instance implementation and
proof terms are deliberately not bulk printed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology
set_option pp.proofs false
set_option pp.maxSteps 200000

namespace TheoremT.Continuum.H1FormAudit

theorem exact_integral_formula (N : ℕ) (Z : ℝ)
    (ψ : PiLp 2 (fun _ : (Fin N → Fin 2) =>
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))) (q : ℝ) :
    coulombH1FormValue N Z ψ q ↔
      (∀ π : Equiv.Perm (Fin N), ∀ σ : Fin N → Fin 2,
        pullback π (ψ (σ ∘ π)) = permutationSign π • ψ σ) ∧
      ∃ d : (Fin N × Fin 3) → PiLp 2 (fun _ : (Fin N → Fin 2) =>
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
        (∀ σ k, ∀ φ : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ x, φ x • d k σ x) =
            -(∫ x, (fderiv ℝ φ x (PiLp.single 2 k 1)) • ψ σ x)) ∧
        q = (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) +
          ∑ σ : Fin N → Fin 2, ∫ x,
            (-Z * (∑ i : Fin N, ‖position x i‖⁻¹) +
              ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
                ‖position x i - position x j‖⁻¹) * ‖ψ σ x‖^2 :=
  coulombH1FormValue_iff_integral

theorem exact_domain (N : ℕ) (Z : ℝ) (ψ : SpinSpace N) :
    (∃! q : ℝ, coulombH1FormValue N Z ψ q) ↔
      (∀ π : Equiv.Perm (Fin N), ∀ σ : Fin N → Fin 2,
        pullback π (ψ (σ ∘ π)) = permutationSign π • ψ σ) ∧
      ∀ σ : Fin N → Fin 2, ∃ d : (Fin N × Fin 3) →
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))),
        ∀ k, ∀ φ : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ x, φ x • d k x) =
            -(∫ x, (fderiv ℝ φ x (PiLp.single 2 k 1)) • ψ σ x) :=
  coulombH1FormValue_existsUnique_iff Z ψ

theorem exact_normalized_infimum (N : ℕ) (Z : ℝ) :
    sInf {e : EReal | ∃ ψ : SpinSpace N, ∃ q : ℝ, ‖ψ‖ = 1 ∧
      coulombH1FormValue N Z ψ q ∧ e = (q : EReal)} =
    sInf {e : EReal | ∃ ψ h : SpinSpace N, ‖ψ‖ = 1 ∧
      hamiltonianGraph N Z ψ h ∧ e = (rayleighNumerator ψ h : EReal)} :=
  formGroundEnergy_eq_variationalGroundEnergy N Z

#print exact_integral_formula
#print exact_domain
#print exact_normalized_infimum
#print TheoremT.Continuum.coulombH1Energy
#print TheoremT.Continuum.coulombH1FormValue
#print TheoremT.Continuum.coulombH1LowerBounds_eq_operatorLowerBounds
#print TheoremT.Continuum.coulombH1Energy_tendsto
#print TheoremT.Continuum.coulomb_potential_energy_integrable
#print TheoremT.Continuum.coulombH1FormValue_eq_graph_energy
#print axioms exact_integral_formula
#print axioms exact_domain
#print axioms exact_normalized_infimum
#print axioms TheoremT.Continuum.coulombH1LowerBounds_eq_operatorLowerBounds
#print axioms TheoremT.Continuum.coulombH1Energy_tendsto
#print axioms TheoremT.Continuum.coulomb_potential_energy_integrable
#print axioms TheoremT.Continuum.coulombH1FormValue_eq_graph_energy

end TheoremT.Continuum.H1FormAudit
