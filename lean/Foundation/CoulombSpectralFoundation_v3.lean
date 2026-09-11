import CoulombSpectralBottom_v2
import NonrealResolvent_v2
import CoulombH1Infimum_v1
import CoulombSharpSemibounded_v1
import HardyGroundNonpositive_v1

/-! Full continuum F02--F04 composition, on the unchanged physical spaces.
The spectrum is defined by failure of a bounded two-sided inverse into the
actual domain. Its reality is proved, not imposed by definition. The H¹ form
and original H² graph infima equal that spectral infimum. No binding,
attainment, uniqueness, gap, approximation rate or algorithm is asserted. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.Continuum

def spectralGroundEnergy (N : ℕ) (Z : ℝ) : EReal :=
  sInf {e : EReal | ∃ z : ℂ,
    z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z) ∧
    e = (z.re : EReal)}

theorem coulomb_spectrum_real (N : ℕ) (Z : ℝ) {z : ℂ}
    (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z)) :
    z.im = 0 :=
  TheoremT.OperatorTheory.unboundedSpectrum_im_eq_zero _
    (coulombPartialOperator_selfAdjoint N Z) hz

theorem coulomb_spectrum_re_lower_bound (N : ℕ) (Z : ℝ) {z : ℂ}
    (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z)) :
    (variationalGroundEnergy N Z).toReal ≤ z.re := by
  have hi := coulomb_spectrum_real N Z hz
  have heq : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hi]
  apply (coulomb_variational_energy_least_real_spectrum N Z).2
  change (z.re : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z)
  rwa [heq]

theorem spectralGroundEnergy_eq_variationalGroundEnergy (N : ℕ) (Z : ℝ) :
    spectralGroundEnergy N Z = variationalGroundEnergy N Z := by
  have hfinite := variational_ground_energy_finite N Z
  have hc := EReal.coe_toReal hfinite.1 hfinite.2
  calc
    spectralGroundEnergy N Z = ((variationalGroundEnergy N Z).toReal : EReal) := by
      apply le_antisymm
      · exact sInf_le ⟨((variationalGroundEnergy N Z).toReal : ℂ),
          coulomb_variational_energy_mem_spectrum N Z, by simp⟩
      · apply le_sInf
        rintro e ⟨z,hz,rfl⟩
        exact_mod_cast coulomb_spectrum_re_lower_bound N Z hz
    _ = variationalGroundEnergy N Z := hc

theorem formGroundEnergy_eq_spectralGroundEnergy (N : ℕ) (Z : ℝ) :
    formGroundEnergy N Z = spectralGroundEnergy N Z := by
  rw [formGroundEnergy_eq_variationalGroundEnergy,
    spectralGroundEnergy_eq_variationalGroundEnergy]

/-- The complete shared continuum theorem. All physical and spectral
conclusions are proved for every finite N and real Z without extra premises. -/
theorem coulomb_shared_continuum_foundation (N : ℕ) (Z : ℝ) :
    IsSelfAdjoint (coulombPartialOperator N Z) ∧
    ((coulombPartialOperator N Z).domain : Set (FermionicSpace N)) =
      {ψ | ∀ σ, HasH2 (ψ.val σ)} ∧
    ∃ E : ℝ, variationalGroundEnergy N Z = (E : EReal) ∧
      formGroundEnergy N Z = (E : EReal) ∧
      spectralGroundEnergy N Z = (E : EReal) ∧
      -(N : ℝ) * (max Z 0)^2 / 2 ≤ E ∧ E ≤ 0 ∧
      (E : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z) ∧
      ∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z),
        z.im = 0 ∧ E ≤ z.re := by
  let E : ℝ := (variationalGroundEnergy N Z).toReal
  have hfinite := variational_ground_energy_finite N Z
  have hE : variationalGroundEnergy N Z = (E : EReal) :=
    (EReal.coe_toReal hfinite.1 hfinite.2).symm
  refine ⟨coulombPartialOperator_selfAdjoint N Z,
    coulombPartialOperator_domain_eq_H2 N Z,E,hE,?_,?_,?_,?_,
    coulomb_variational_energy_mem_spectrum N Z,?_⟩
  · exact (formGroundEnergy_eq_variationalGroundEnergy N Z).trans hE
  · exact (spectralGroundEnergy_eq_variationalGroundEnergy N Z).trans hE
  · have hb := variational_ground_energy_sharp_lower_bound N Z
    rw [hE] at hb
    exact_mod_cast hb
  · have hb := variational_ground_energy_nonpositive N Z
    rw [hE] at hb
    exact_mod_cast hb
  · intro z hz
    exact ⟨coulomb_spectrum_real N Z hz,coulomb_spectrum_re_lower_bound N Z hz⟩

#print axioms spectralGroundEnergy
#print axioms coulomb_spectrum_real
#print axioms formGroundEnergy_eq_spectralGroundEnergy
#print axioms coulomb_shared_continuum_foundation
end TheoremT.Continuum
