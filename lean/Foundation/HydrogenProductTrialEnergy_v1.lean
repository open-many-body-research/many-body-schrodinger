import HydrogenProductTrialDomain_v1
import HydrogenGradientNorm_v1
import TwoElectronProductRepulsion_v1
import TwoElectronProductForm_v1
import TwoElectronSingletForm_v1
import TwoElectronOperatorComparison_v1

/-! Certified physical energy of the charge-matched hydrogen product trial.
The repulsion is bounded by relative-coordinate uncertainty, not assigned its
unformalized exact moment. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
open TheoremT.Polar

def hydrogenProductRepulsion (Z : ℝ) (hZ : 0 < Z) : ℝ :=
  ∫ x, ‖twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hZ)
    (normalizedPolarGround configuration_one_finrank Z hZ) x‖^2 /
      ‖position x 0 - position x 1‖

theorem hydrogenProductRepulsion_nonneg (Z : ℝ) (hZ : 0 < Z) :
    0 ≤ hydrogenProductRepulsion Z hZ := integral_nonneg (fun x => by positivity)

theorem hydrogenProductRepulsion_sq_le (Z : ℝ) (hZ : 0 < Z) :
    (hydrogenProductRepulsion Z hZ)^2 ≤ Z^2/2 := by
  have h := twoElectronTensor_pair_repulsion_sq
    (normalizedPolarGround configuration_one_finrank Z hZ)
    (normalizedPolarGround_norm configuration_one_finrank Z hZ)
    (normalizedHydrogenGradient Z hZ) (normalizedHydrogenGradient_weak Z hZ)
  rw [normalizedHydrogenGradient_electron_norm_sum] at h
  simpa only [hydrogenProductRepulsion,one_div,mul_comm,div_eq_mul_inv,one_mul] using h

theorem normalizedHydrogen_formValue (Z : ℝ) (hZ : 0 < Z) :
    scalarCoulombH1FormValue 1 Z (normalizedPolarGround configuration_one_finrank Z hZ)
      (-(Z^2/2)) := by
  have h := scalarHamiltonianGraph_formValue (normalizedPolarGround_eigenGraph Z hZ)
  simpa [inner_smul_right,inner_self_eq_norm_sq_to_K,
    normalizedPolarGround_norm configuration_one_finrank Z hZ,← Complex.ofReal_pow] using h

theorem hydrogenProductTrial_formValue (Z : ℝ) (hZ : 0 < Z) :
    coulombH1FormValue 2 Z ((hydrogenProductTrial Z Z hZ : FermionicSpace 2).val)
      (-Z^2 + hydrogenProductRepulsion Z hZ) := by
  have h := twoElectronSinglet_formValue Z
    (normalizedPolarGround configuration_one_finrank Z hZ)
    (twoElectronTensor_formValue_unit Z _
      (normalizedPolarGround_norm configuration_one_finrank Z hZ) (normalizedHydrogen_formValue Z hZ))
  convert h using 1 <;> first | rfl | (unfold hydrogenProductRepulsion; ring)

theorem hydrogenProductTrial_energy (Z : ℝ) (hZ : 0 < Z) :
    (inner ℂ (hydrogenProductTrial Z Z hZ : FermionicSpace 2)
      (coulombPartialOperator 2 Z (hydrogenProductTrial Z Z hZ))).re =
        -Z^2 + hydrogenProductRepulsion Z hZ := by
  have h := coulombH1FormValue_eq_graph_energy (hydrogenProductTrial_formValue Z hZ)
    (coulombPartialOperator_apply_graph 2 Z (hydrogenProductTrial Z Z hZ))
  rw [rayleighNumerator_eq_re_complex_inner] at h
  exact h.symm

theorem hydrogenProductTrial_strict (Z : ℝ) (hZ : 0 < Z) (hsep : 32 < 9*Z^2) :
    (inner ℂ (hydrogenProductTrial Z Z hZ : FermionicSpace 2)
      (coulombPartialOperator 2 Z (hydrogenProductTrial Z Z hZ))).re < -(5*Z^2/8) := by
  rw [hydrogenProductTrial_energy]
  have hR := hydrogenProductRepulsion_sq_le Z hZ
  have hR0 := hydrogenProductRepulsion_nonneg Z hZ
  have hZ2 : 0 < Z^2 := sq_pos_of_pos hZ
  have hs : Z^2/2 < (3*Z^2/8)^2 := by
    nlinarith [mul_pos hZ2 (sub_pos.mpr hsep)]
  have hlt : hydrogenProductRepulsion Z hZ < 3*Z^2/8 :=
    (sq_lt_sq₀ hR0 (by positivity)).mp (hR.trans_lt hs)
  linarith

#print axioms hydrogenProductRepulsion_sq_le
#print axioms hydrogenProductTrial_energy
#print axioms hydrogenProductTrial_strict
end TheoremT.Continuum
