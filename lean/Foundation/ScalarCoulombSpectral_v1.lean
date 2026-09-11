import ScalarCoulombSelfAdjoint_v1
import ScalarCoulombVariational_v1
import NonrealResolvent_v2

/-! The scalar graph variational infimum equals the bottom of the actual
bounded-two-sided-inverse spectrum on the exact weak-H² domain. The reality
of every spectral point is proved. No eigenvector or binding is assumed. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.Continuum

def scalarSpectralGroundEnergy (N : ℕ) (Z : ℝ) : EReal :=
  sInf {e : EReal | ∃ z : ℂ,
    z ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z) ∧
    e = (z.re : EReal)}

theorem scalar_coulomb_spectrum_real (N : ℕ) (Z : ℝ) {z : ℂ}
    (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z)) :
    z.im = 0 :=
  TheoremT.OperatorTheory.unboundedSpectrum_im_eq_zero _
    (scalarCoulombOperator_selfAdjoint N Z) hz

theorem scalar_variational_least_real_spectrum (N : ℕ) (Z : ℝ) :
    IsLeast {t : ℝ | (t : ℂ) ∈
      TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z)}
      (scalarVariationalGroundEnergy N Z).toReal :=
  TheoremT.OperatorTheory.isLeast_real_spectrum_of_greatest_lower_bound _
    (scalarCoulombOperator_selfAdjoint N Z) (scalar_variational_isGreatest_operatorLowerBounds N Z)

theorem scalar_variational_mem_spectrum (N : ℕ) (Z : ℝ) :
    ((scalarVariationalGroundEnergy N Z).toReal : ℂ) ∈
      TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z) :=
  (scalar_variational_least_real_spectrum N Z).1

theorem scalar_coulomb_spectrum_re_lower_bound (N : ℕ) (Z : ℝ) {z : ℂ}
    (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z)) :
    (scalarVariationalGroundEnergy N Z).toReal ≤ z.re := by
  have hi := scalar_coulomb_spectrum_real N Z hz
  have heq : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hi]
  apply (scalar_variational_least_real_spectrum N Z).2
  change (z.re : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z)
  rwa [heq]

theorem scalarSpectralGroundEnergy_eq_variational (N : ℕ) (Z : ℝ) :
    scalarSpectralGroundEnergy N Z = scalarVariationalGroundEnergy N Z := by
  have hf := scalar_variational_ground_finite N Z
  have hc := EReal.coe_toReal hf.1 hf.2
  calc
    scalarSpectralGroundEnergy N Z = ((scalarVariationalGroundEnergy N Z).toReal : EReal) := by
      apply le_antisymm
      · exact sInf_le ⟨((scalarVariationalGroundEnergy N Z).toReal : ℂ),
          scalar_variational_mem_spectrum N Z,by simp⟩
      · apply le_sInf
        rintro e ⟨z,hz,rfl⟩
        exact_mod_cast scalar_coulomb_spectrum_re_lower_bound N Z hz
    _ = scalarVariationalGroundEnergy N Z := hc

/-- Actual all-N scalar Coulomb realization and finite spectral bottom, with no
assumptions other than finite N and real Z. The H¹-form identification follows
in a separate module from actual scalar H¹ approximation. -/
theorem scalar_coulomb_selfAdjoint_H2_spectral_bottom (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (scalarCoulombOperator N Z) ∧
    ((scalarCoulombOperator N Z).domain : Set (SpatialL2 N)) = {f | HasH2 f} ∧
    ∃ E : ℝ, scalarVariationalGroundEnergy N Z = (E : EReal) ∧
      scalarSpectralGroundEnergy N Z = (E : EReal) ∧
      -(N : ℝ)*(max Z 0)^2/2 ≤ E ∧
      (E : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z) ∧
      ∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (scalarCoulombOperator N Z),
        z.im = 0 ∧ E ≤ z.re := by
  let E := (scalarVariationalGroundEnergy N Z).toReal
  have hf := scalar_variational_ground_finite N Z
  have hE : scalarVariationalGroundEnergy N Z = (E : EReal) :=
    (EReal.coe_toReal hf.1 hf.2).symm
  refine ⟨scalarCoulombOperator_selfAdjoint N Z,scalarCoulombOperator_domain_eq_H2 N Z,
    E,hE,(scalarSpectralGroundEnergy_eq_variational N Z).trans hE,?_,
    scalar_variational_mem_spectrum N Z,?_⟩
  · have hb := scalar_variational_ground_sharp_lower_bound N Z
    rw [hE] at hb
    exact_mod_cast hb
  · intro z hz
    exact ⟨scalar_coulomb_spectrum_real N Z hz,scalar_coulomb_spectrum_re_lower_bound N Z hz⟩

#print axioms scalar_coulomb_spectrum_real
#print axioms scalar_variational_least_real_spectrum
#print axioms scalarSpectralGroundEnergy_eq_variational
#print axioms scalar_coulomb_selfAdjoint_H2_spectral_bottom
end TheoremT.Continuum
