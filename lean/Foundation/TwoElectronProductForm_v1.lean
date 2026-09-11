import CoulombTwoElectronExpectation_v1
import TwoElectronTensorNuclear_v1
import ScalarCoulombForm_v1

/-! Exact physical form value of a repeated normalized orbital product. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_one_potential_energy (Z : ℝ) (f : SpatialL2 1) :
    (∫ x, coulombPotential 1 Z x * ‖f x‖^2) =
      -Z * ∫ x, ‖f x‖^2 / ‖position x 0‖ := by
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [coulombPotential_one_electron,position_one_norm]
  ring

theorem scalar_one_form_energy (Z : ℝ) (f : SpatialL2 1)
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k)
    {q : ℝ} (hq : scalarCoulombH1FormValue 1 Z f q) :
    q = (1/2 : ℝ) * (∑ k : Coordinate 1, ‖d k‖^2) -
      Z * ∫ x, ‖f x‖^2 / ‖position x 0‖ := by
  obtain ⟨d',hd',he⟩ := scalarCoulombH1FormValue_iff_integral.mp hq
  have hdd : d' = d := funext (fun k => weakPartial_unique (hd' k) (hd k))
  rw [hdd,scalar_one_potential_energy] at he
  simpa only [neg_mul,sub_eq_add_neg] using he

theorem twoElectronTensor_formValue_unit (Z : ℝ) (f : SpatialL2 1) (hf : ‖f‖=1)
    {q : ℝ} (hq : scalarCoulombH1FormValue 1 Z f q) :
    scalarCoulombH1FormValue 2 Z (twoElectronTensor f f)
      (2*q + ∫ x, ‖twoElectronTensor f f x‖^2 / ‖position x 0 - position x 1‖) := by
  obtain ⟨d,hd,he⟩ := scalarCoulombH1FormValue_iff_integral.mp hq
  have h1 := scalar_one_form_energy Z f d hd hq
  apply scalarCoulombH1FormValue_iff_integral.mpr
  refine ⟨twoElectronTensorGradient f f d d,twoElectronTensorGradient_weak f f d d hd hd,?_⟩
  rw [twoElectronTensorGradient_norm_sum,
    twoElectron_potential_energy_decomposition Z _ _ (twoElectronTensorGradient_weak f f d d hd hd),
    twoElectronTensor_nuclear_first,twoElectronTensor_nuclear_second,hf,h1]
  ring

#print axioms scalar_one_potential_energy
#print axioms scalar_one_form_energy
#print axioms twoElectronTensor_formValue_unit
end TheoremT.Continuum
