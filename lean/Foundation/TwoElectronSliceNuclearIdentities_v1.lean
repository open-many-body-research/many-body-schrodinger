import TwoElectronSliceL2Identities_v1
import CoulombAttractiveExpectation_v1
import HydrogenRadialTrace_v1

/-! Exact untruncated nuclear energy integrals in the two actual H1 slices. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectronReassemble_first_radius (x y : Configuration 1) :
    ‖position (twoElectronConfigurationProduct.symm (x,y)) (0 : Fin 2)‖ = ‖x‖ := by
  rw [← twoElectronConfigurationProduct_fst_position]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact position_one_norm x

theorem twoElectronReassemble_second_radius (x y : Configuration 1) :
    ‖position (twoElectronConfigurationProduct.symm (x,y)) (1 : Fin 2)‖ = ‖y‖ := by
  rw [← twoElectronConfigurationProduct_snd_position]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact position_one_norm y

def twoElectronFirstSlice_nuclear (F : SpatialL2 2) (y : Configuration 1) : ℝ :=
  ∫ x, ‖twoElectronFirstSlice F y x‖ ^ 2 / ‖x‖

def twoElectronSecondSlice_nuclear (F : SpatialL2 2) (x : Configuration 1) : ℝ :=
  ∫ y, ‖twoElectronSecondSlice F x y‖ ^ 2 / ‖y‖

theorem twoElectronFirstSlice_nuclear_ae (F : SpatialL2 2) :
    twoElectronFirstSlice_nuclear F =ᵐ[volume] fun y =>
      ∫ x, ‖F (twoElectronConfigurationProduct.symm (x,y))‖ ^ 2 /
        ‖position (twoElectronConfigurationProduct.symm (x,y)) (0 : Fin 2)‖ := by
  filter_upwards [twoElectronFirstSlice_ae_of_ae F F (Filter.Eventually.of_forall (fun _ => rfl))]
    with y hy
  apply integral_congr_ae
  filter_upwards [hy] with x hx
  rw [hx,twoElectronReassemble_first_radius]

theorem twoElectronSecondSlice_nuclear_ae (F : SpatialL2 2) :
    twoElectronSecondSlice_nuclear F =ᵐ[volume] fun x =>
      ∫ y, ‖F (twoElectronConfigurationProduct.symm (x,y))‖ ^ 2 /
        ‖position (twoElectronConfigurationProduct.symm (x,y)) (1 : Fin 2)‖ := by
  filter_upwards [twoElectronSecondSlice_ae_coe F] with x hx
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  rw [hy,twoElectronReassemble_second_radius]

theorem twoElectronFirstSlice_nuclear_integrable (F : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial F (d k) k) :
    Integrable (twoElectronFirstSlice_nuclear F) volume := by
  have hi := nuclear_potential_energy_integrable_of_weakH1 (0 : Fin 2) F d hd
  have hp := twoElectronConfigurationProduct_symm_measurePreserving.integrable_comp_of_integrable hi
  apply hp.integral_prod_right.congr
  exact (twoElectronFirstSlice_nuclear_ae F).symm

theorem twoElectronSecondSlice_nuclear_integrable (F : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial F (d k) k) :
    Integrable (twoElectronSecondSlice_nuclear F) volume := by
  have hi := nuclear_potential_energy_integrable_of_weakH1 (1 : Fin 2) F d hd
  have hp := twoElectronConfigurationProduct_symm_measurePreserving.integrable_comp_of_integrable hi
  apply hp.integral_prod_left.congr
  exact (twoElectronSecondSlice_nuclear_ae F).symm

theorem twoElectronFirstSlice_nuclear_integral (F : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial F (d k) k) :
    (∫ y, twoElectronFirstSlice_nuclear F y) =
      ∫ q, ‖F q‖ ^ 2 / ‖position q (0 : Fin 2)‖ := by
  have hi := nuclear_potential_energy_integrable_of_weakH1 (0 : Fin 2) F d hd
  have hp := twoElectronConfigurationProduct_symm_measurePreserving.integrable_comp_of_integrable hi
  rw [integral_congr_ae (twoElectronFirstSlice_nuclear_ae F)]
  dsimp only [Function.comp_def] at hp
  rw [← integral_prod_symm _ hp]
  exact twoElectronConfigurationProduct_symm_measurePreserving.integral_comp
    twoElectronConfigurationProduct.symm.toHomeomorph.measurableEmbedding
    (fun q : Configuration 2 => ‖F q‖^2 / ‖position q (0 : Fin 2)‖)

theorem twoElectronSecondSlice_nuclear_integral (F : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial F (d k) k) :
    (∫ x, twoElectronSecondSlice_nuclear F x) =
      ∫ q, ‖F q‖ ^ 2 / ‖position q (1 : Fin 2)‖ := by
  have hi := nuclear_potential_energy_integrable_of_weakH1 (1 : Fin 2) F d hd
  have hp := twoElectronConfigurationProduct_symm_measurePreserving.integrable_comp_of_integrable hi
  rw [integral_congr_ae (twoElectronSecondSlice_nuclear_ae F)]
  dsimp only [Function.comp_def] at hp
  rw [← integral_prod _ hp]
  exact twoElectronConfigurationProduct_symm_measurePreserving.integral_comp
    twoElectronConfigurationProduct.symm.toHomeomorph.measurableEmbedding
    (fun q : Configuration 2 => ‖F q‖^2 / ‖position q (1 : Fin 2)‖)

#print axioms twoElectronFirstSlice_nuclear_integrable
#print axioms twoElectronSecondSlice_nuclear_integrable
#print axioms twoElectronFirstSlice_nuclear_integral
#print axioms twoElectronSecondSlice_nuclear_integral
end TheoremT.Continuum
