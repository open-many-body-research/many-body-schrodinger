import HydrogenProductTrialEnergy_v1
import HardyRankOneTemple_v1

/-!
A screened physical hydrogen product improves the published two-electron
charge range without assuming the unformalized exact repulsion moment.
The operator, weak derivatives, spin singlet, and operator-domain trial are
all the original foundation objects. This is partial progress on S2.4;
the exact-repulsion range remains open.
-/
noncomputable section
open MeasureTheory
namespace ManyBody.S2
open TheoremT.Continuum TheoremT.Polar

/-- The normalized hydrogen orbital has its exact nuclear expectation. -/
theorem normalizedHydrogen_nuclearMoment (α : ℝ) (hα : 0 < α) :
    (∫ x, ‖normalizedPolarGround configuration_one_finrank α hα x‖^2 /
      ‖position x 0‖) = α := by
  have h := scalar_one_form_energy α
    (normalizedPolarGround configuration_one_finrank α hα)
    (normalizedHydrogenGradient α hα) (normalizedHydrogenGradient_weak α hα)
    (normalizedHydrogen_formValue α hα)
  rw [normalizedHydrogenGradient_norm_sum] at h
  have he : α * (∫ x, ‖normalizedPolarGround configuration_one_finrank α hα x‖^2 /
      ‖position x 0‖) = α * α := by nlinarith
  exact mul_left_cancel₀ (ne_of_gt hα) he

/-- Exact one-body form energy at physical charge Z and independent trial scale α. -/
theorem screenedHydrogen_formValue (Z α : ℝ) (hα : 0 < α) :
    scalarCoulombH1FormValue 1 Z
      (normalizedPolarGround configuration_one_finrank α hα)
      (α^2/2 - Z*α) := by
  apply scalarCoulombH1FormValue_iff_integral.mpr
  refine ⟨normalizedHydrogenGradient α hα,normalizedHydrogenGradient_weak α hα,?_⟩
  rw [normalizedHydrogenGradient_norm_sum,scalar_one_potential_energy,
    normalizedHydrogen_nuclearMoment]
  ring

/-- Exact physical energy of the normalized screened singlet, retaining actual repulsion. -/
theorem hydrogenProductTrial_scaled_energy (Z α : ℝ) (hα : 0 < α) :
    (inner ℂ (hydrogenProductTrial Z α hα : FermionicSpace 2)
      (coulombPartialOperator 2 Z (hydrogenProductTrial Z α hα))).re =
        α^2 - 2*Z*α + hydrogenProductRepulsion α hα := by
  have h := twoElectronSinglet_formValue Z
    (normalizedPolarGround configuration_one_finrank α hα)
    (twoElectronTensor_formValue_unit Z _
      (normalizedPolarGround_norm configuration_one_finrank α hα)
      (screenedHydrogen_formValue Z α hα))
  have hf : coulombH1FormValue 2 Z
      ((hydrogenProductTrial Z α hα : FermionicSpace 2).val)
      (α^2 - 2*Z*α + hydrogenProductRepulsion α hα) := by
    convert h using 1 <;> first | rfl | (unfold hydrogenProductRepulsion; ring)
  have he := coulombH1FormValue_eq_graph_energy hf
    (coulombPartialOperator_apply_graph 2 Z (hydrogenProductTrial Z α hα))
  rw [rayleighNumerator_eq_re_complex_inner] at he
  exact he.symm

/-- The foundation's relative-coordinate uncertainty bounds actual product repulsion. -/
theorem hydrogenProductRepulsion_upper (α : ℝ) (hα : 0 < α) :
    hydrogenProductRepulsion α hα ≤ Real.sqrt 2 / 2 * α := by
  have hs := hydrogenProductRepulsion_sq_le α hα
  have h0 := hydrogenProductRepulsion_nonneg α hα
  have ht : 0 ≤ Real.sqrt 2 / 2 * α := by positivity
  apply (sq_le_sq₀ h0 ht).mp
  have hr : (Real.sqrt 2 / 2 * α)^2 = α^2/2 := by
    rw [mul_pow,div_pow,Real.sq_sqrt (by norm_num)]
    ring
  rwa [hr]

/-- Optimizing the uncertainty bound yields a strict, explicitly screened trial. -/
theorem screenedTrial_energy_upper (Z : ℝ) (hα : 0 < Z - Real.sqrt 2 / 4) :
    (inner ℂ
      (hydrogenProductTrial Z (Z - Real.sqrt 2 / 4) hα : FermionicSpace 2)
      (coulombPartialOperator 2 Z
        (hydrogenProductTrial Z (Z - Real.sqrt 2 / 4) hα))).re ≤
      -(Z - Real.sqrt 2 / 4)^2 := by
  rw [hydrogenProductTrial_scaled_energy]
  have h := hydrogenProductRepulsion_upper (Z - Real.sqrt 2 / 4) hα
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The explicit upper root of the screened separation quadratic discharges
all charge and trial-scale premises of the physical branch theorem. -/
theorem screened_charge_conditions (Z : ℝ)
    (hZ : (2*Real.sqrt 2 + Real.sqrt 5)/3 < Z) :
    0 < Z ∧ 0 < Z - Real.sqrt 2 / 4 ∧
      5*Z^2/8 < (Z - Real.sqrt 2 / 4)^2 := by
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h5p : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h2s : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have h5s : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hleft : 0 < 3*Z - 2*Real.sqrt 2 - Real.sqrt 5 := by linarith
  have hright : 0 < 3*Z - 2*Real.sqrt 2 + Real.sqrt 5 := by linarith
  refine ⟨by linarith,by linarith,?_⟩
  nlinarith [mul_pos hleft hright]

/-- A physical ground branch in the improved screened-uncertainty charge range.
Its eigenstate is normalized, its ground eigenspace is a single complex line,
and every other spectral point is at or above the hydrogenic separator. -/
theorem screened_ground_branch (Z : ℝ) (hZ : 0 < Z)
    (hα : 0 < Z - Real.sqrt 2 / 4)
    (hsep : 5*Z^2/8 < (Z - Real.sqrt 2 / 4)^2) :
    (variationalGroundEnergy 2 Z).toReal ≤ -(Z - Real.sqrt 2 / 4)^2 ∧
    (variationalGroundEnergy 2 Z).toReal < -(5*Z^2/8) ∧
    ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      (∀ u : (coulombPartialOperator 2 Z).domain,
        coulombPartialOperator 2 Z u =
          ((variationalGroundEnergy 2 Z).toReal : ℂ) • (u : FermionicSpace 2) →
        (u : FermionicSpace 2) =
          inner ℂ (g : FermionicSpace 2) (u : FermionicSpace 2) • (g : FermionicSpace 2)) ∧
      (∀ w : (coulombPartialOperator 2 Z).domain,
        inner ℂ (g : FermionicSpace 2) (w : FermionicSpace 2) = 0 →
        -(5*Z^2/8) * ‖(w : FermionicSpace 2)‖^2 ≤
          (inner ℂ (w : FermionicSpace 2) (coulombPartialOperator 2 Z w)).re) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
        z = ((variationalGroundEnergy 2 Z).toReal : ℂ) ∨ -(5*Z^2/8) ≤ z.re) := by
  let trial := hydrogenProductTrial Z (Z - Real.sqrt 2 / 4) hα
  have hn := hydrogenProductTrial_norm Z (Z - Real.sqrt 2 / 4) hα
  have hu := screenedTrial_energy_upper Z hα
  have hstrict : -(Z - Real.sqrt 2 / 4)^2 < -(5*Z^2/8) := by linarith
  obtain ⟨hgap,g,hg,hEg,hcomp,hspec⟩ :=
    twoElectron_ground_branch_of_strict_trial Z hZ trial hn (hu.trans_lt hstrict)
  refine ⟨(coulomb_ground_energy_le_domain_rayleigh 2 Z trial hn).trans hu,
    hgap,g,hg,hEg,?_,hcomp,hspec⟩
  exact fun u hEu => TheoremT.OperatorTheory.ground_complement_eigenspace_rank_one
    (coulombPartialOperator 2 Z) g hg _ _ hEg hgap hcomp u hEu

/-- The improved branch for every charge above the explicit screened threshold. -/
theorem screened_ground_branch_above_threshold (Z : ℝ)
    (hZ : (2*Real.sqrt 2 + Real.sqrt 5)/3 < Z) :
    (variationalGroundEnergy 2 Z).toReal ≤ -(Z - Real.sqrt 2 / 4)^2 ∧
    (variationalGroundEnergy 2 Z).toReal < -(5*Z^2/8) ∧
    ∃ g : (coulombPartialOperator 2 Z).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 Z g =
        ((variationalGroundEnergy 2 Z).toReal : ℂ) • (g : FermionicSpace 2) ∧
      (∀ u : (coulombPartialOperator 2 Z).domain,
        coulombPartialOperator 2 Z u =
          ((variationalGroundEnergy 2 Z).toReal : ℂ) • (u : FermionicSpace 2) →
        (u : FermionicSpace 2) =
          inner ℂ (g : FermionicSpace 2) (u : FermionicSpace 2) • (g : FermionicSpace 2)) ∧
      (∀ w : (coulombPartialOperator 2 Z).domain,
        inner ℂ (g : FermionicSpace 2) (w : FermionicSpace 2) = 0 →
        -(5*Z^2/8) * ‖(w : FermionicSpace 2)‖^2 ≤
          (inner ℂ (w : FermionicSpace 2) (coulombPartialOperator 2 Z w)).re) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
        z = ((variationalGroundEnergy 2 Z).toReal : ℂ) ∨ -(5*Z^2/8) ≤ z.re) := by
  obtain ⟨hZ0,hα,hsep⟩ := screened_charge_conditions Z hZ
  exact screened_ground_branch Z hZ0 hα hsep

/-- An explicit rational charge omitted by the old hypothesis has a simple,
attained physical ground energy strictly below the same spectral separator. -/
theorem screened_ground_branch_seven_fourths :
    ¬ (32 < 9*(7/4 : ℝ)^2) ∧
    (variationalGroundEnergy 2 (7/4)).toReal ≤ -(7/4 - Real.sqrt 2 / 4)^2 ∧
    (variationalGroundEnergy 2 (7/4)).toReal < -(245/128 : ℝ) ∧
    ∃ g : (coulombPartialOperator 2 (7/4)).domain,
      ‖(g : FermionicSpace 2)‖ = 1 ∧
      coulombPartialOperator 2 (7/4) g =
        ((variationalGroundEnergy 2 (7/4)).toReal : ℂ) • (g : FermionicSpace 2) ∧
      (∀ u : (coulombPartialOperator 2 (7/4)).domain,
        coulombPartialOperator 2 (7/4) u =
          ((variationalGroundEnergy 2 (7/4)).toReal : ℂ) • (u : FermionicSpace 2) →
        (u : FermionicSpace 2) =
          inner ℂ (g : FermionicSpace 2) (u : FermionicSpace 2) • (g : FermionicSpace 2)) ∧
      (∀ w : (coulombPartialOperator 2 (7/4)).domain,
        inner ℂ (g : FermionicSpace 2) (w : FermionicSpace 2) = 0 →
        -(245/128 : ℝ) * ‖(w : FermionicSpace 2)‖^2 ≤
          (inner ℂ (w : FermionicSpace 2) (coulombPartialOperator 2 (7/4) w)).re) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 (7/4)),
        z = ((variationalGroundEnergy 2 (7/4)).toReal : ℂ) ∨ -(245/128 : ℝ) ≤ z.re) := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hslt : Real.sqrt 2 < 10/7 := by nlinarith
  have hα : 0 < (7/4 : ℝ) - Real.sqrt 2 / 4 := by linarith
  have hsep : 5*(7/4 : ℝ)^2/8 < (7/4 - Real.sqrt 2 / 4)^2 := by nlinarith
  refine ⟨by norm_num,?_⟩
  have hbranch := screened_ground_branch (7/4) (by norm_num) hα hsep
  have hβ : 5*(7/4 : ℝ)^2/8 = 245/128 := by norm_num
  rw [hβ] at hbranch
  exact hbranch

#print axioms normalizedHydrogen_nuclearMoment
#print axioms screenedHydrogen_formValue
#print axioms hydrogenProductTrial_scaled_energy
#print axioms hydrogenProductRepulsion_upper
#print axioms screenedTrial_energy_upper
#print axioms screened_charge_conditions
#print axioms screened_ground_branch_above_threshold
#print axioms screened_ground_branch
#print axioms screened_ground_branch_seven_fourths
end ManyBody.S2
