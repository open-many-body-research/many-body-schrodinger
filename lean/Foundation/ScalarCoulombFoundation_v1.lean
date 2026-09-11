import ScalarCoulombSpectral_v1
import ScalarCoulombFormInfimum_v1
import ScalarFermionicEnergyComparison_v1

/-! Complete scalar continuum realization needed by the two-electron spatial
comparison program. The model is the unrestricted complex scalar L² space,
not the fermionic space. Its operator is the original scalar Coulomb graph on
exact weak H²; its form uses actual weak H¹ derivatives and physical Coulomb
multiplication. No binding, ground-state attainment or simplicity is asserted. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.Continuum

theorem scalarFormGroundEnergy_eq_spectralGroundEnergy (N : ℕ) (Z : ℝ) :
    scalarFormGroundEnergy N Z = scalarSpectralGroundEnergy N Z := by
  rw [scalarFormGroundEnergy_eq_variationalGroundEnergy,scalarSpectralGroundEnergy_eq_variational]

theorem scalarCoulombOperator_closed (N : ℕ) (Z : ℝ) :
    (scalarCoulombOperator N Z).IsClosed :=
  (scalarCoulombOperator_selfAdjoint N Z).isClosed

/-- All scalar continuum conclusions are proved for every finite N and real Z.
The explicit simultaneous spin/spatial fermionic restriction has its separate
realization; its energy is bounded below by this scalar energy. -/
theorem scalar_coulomb_continuum_foundation (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (scalarCoulombOperator N Z) ∧
    ((scalarCoulombOperator N Z).domain : Set (SpatialL2 N)) = {f | HasH2 f} ∧
    (∀ f : SpatialL2 N, (∃! q : ℝ, scalarCoulombH1FormValue N Z f q) ↔ HasH1 f) ∧
    ∃ E : ℝ, scalarVariationalGroundEnergy N Z = (E : EReal) ∧
      scalarFormGroundEnergy N Z = (E : EReal) ∧
      scalarSpectralGroundEnergy N Z = (E : EReal) ∧
      -(N : ℝ)*(max Z 0)^2/2 ≤ E ∧ E ≤ 0 ∧
      (E : EReal) ≤ variationalGroundEnergy N Z ∧
      (E : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z) ∧
      ∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z),
        z.im = 0 ∧ E ≤ z.re := by
  let E := (scalarVariationalGroundEnergy N Z).toReal
  have hf := scalar_variational_ground_finite N Z
  have hE : scalarVariationalGroundEnergy N Z = (E : EReal) :=
    (EReal.coe_toReal hf.1 hf.2).symm
  refine ⟨scalarCoulombOperator_selfAdjoint N Z,scalarCoulombOperator_domain_eq_H2 N Z,
    scalarCoulombH1FormValue_existsUnique_iff Z,E,hE,
    (scalarFormGroundEnergy_eq_variationalGroundEnergy N Z).trans hE,
    (scalarSpectralGroundEnergy_eq_variational N Z).trans hE,?_,?_,?_,
    scalar_variational_mem_spectrum N Z,?_⟩
  · have hb := scalar_variational_ground_sharp_lower_bound N Z
    rw [hE] at hb
    exact_mod_cast hb
  · have hb := scalar_variational_ground_nonpositive N Z
    rw [hE] at hb
    exact_mod_cast hb
  · rw [← hE]
    exact scalarVariationalGroundEnergy_le_fermionic N Z
  · intro z hz
    exact ⟨scalar_coulomb_spectrum_real N Z hz,scalar_coulomb_spectrum_re_lower_bound N Z hz⟩

#print axioms scalarFormGroundEnergy_eq_spectralGroundEnergy
#print axioms scalarCoulombOperator_closed
#print axioms scalar_coulomb_continuum_foundation
end TheoremT.Continuum
