import ManyBody.S2.Internal.HydrogenProductDensity
import ManyBody.S2.Internal.RadialCoulombNewton
import ManyBody.S2.Internal.ExponentialRadialMoments
import ManyBody.S2.ScreenedGroundBranch

/-! Exact hydrogen product repulsion in the original continuum model, with no supplied moment hypothesis. The resulting optimized singlet energy completes the S2.4 charge-range improvement and yields a normalized simple physical ground branch for every charge above (20+5*sqrt 10)/24. This does not close the additional hypotheses of Theorem T. -/

noncomputable section
open MeasureTheory Set
namespace ManyBody.S2
open TheoremT.Continuum TheoremT.Polar TheoremT.HydrogenPolynomial
open Internal.Cylindrical Internal.ExponentialRadial

/-- The exact untruncated Coulomb repulsion of the actual normalized hydrogen tensor. -/
theorem hydrogenProductRepulsion_exact (α : ℝ) (hα : 0 < α) :
    hydrogenProductRepulsion α hα = 5*α/8 := by
  have hb : 0 < 2*α := by positivity
  let Q : ℝ → ℝ := fun s => ∫ r : ℝ in Ioi 0,
    r^2*Real.exp (-(2*α)*r)/max r s
  have hd : (∫ y : AngularR3, ∫ x : AngularR3,
      Real.exp (-(2*α)*‖x‖)*Real.exp (-(2*α)*‖y‖)/‖x-y‖) =
      (4*Real.pi) * ∫ y : AngularR3, Real.exp (-(2*α)*‖y‖)*Q ‖y‖ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hydrogenRepulsion_inner_integrable_ae α hα,
      (volume : Measure AngularR3).ae_ne 0] with y hi hy
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hnew := integral_radial_coulomb y hn
      (f := fun r : ℝ => Real.exp (-(2*α)*r)) (by fun_prop)
      (fun r => (Real.exp_pos _).le) (integrable_moment 2 (2*α) hb) hi
    calc
      _ = Real.exp (-(2*α)*‖y‖) *
          ∫ x : AngularR3, Real.exp (-(2*α)*‖x‖)/‖x-y‖ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = Real.exp (-(2*α)*‖y‖) * ((4*Real.pi)*Q ‖y‖) := by rw [hnew]
      _ = _ := by ring
  have hdim : Module.finrank ℝ AngularR3 = 3 := by simp [AngularR3]
  have hr : (∫ y : AngularR3, Real.exp (-(2*α)*‖y‖)*Q ‖y‖) =
      (4*Real.pi) * ∫ s : ℝ in Ioi 0, s^2*Real.exp (-(2*α)*s)*Q s := by
    rw [integral_fun_norm_addHaar (volume : Measure AngularR3)
      (fun s : ℝ => Real.exp (-(2*α)*s)*Q s),hdim,
      unit_ball_volume_real_dim_three hdim]
    norm_num only [Nat.reduceSub,smul_eq_mul,Nat.cast_ofNat]
    have he : (fun s : ℝ => s^2*(Real.exp (-(2*α)*s)*Q s)) =
        (fun s : ℝ => s^2*Real.exp (-(2*α)*s)*Q s) := by funext s; ring
    rw [he]
    ring
  rw [hydrogenProductRepulsion_eq_double_integral,hd,hr]
  change (α^6/Real.pi^2) * ((4*Real.pi)*((4*Real.pi)*
    (∫ s : ℝ in Ioi 0, s^2*Real.exp (-(2*α)*s)*
      ∫ r : ℝ in Ioi 0, r^2*Real.exp (-(2*α)*r)/max r s))) = _
  rw [integral_newton_double_radial (2*α) hb]
  field_simp [hα.ne',Real.pi_ne_zero]
  ring

#print axioms hydrogenProductRepulsion_exact
/-- Exact energy of the optimally screened physical singlet. -/
theorem exactProductTrial_energy (Z : ℝ) (hα : 0 < Z-5/16) :
    (inner ℂ (hydrogenProductTrial Z (Z-5/16) hα : FermionicSpace 2)
      (coulombPartialOperator 2 Z (hydrogenProductTrial Z (Z-5/16) hα))).re =
        -(Z-5/16)^2 := by
  rw [hydrogenProductTrial_scaled_energy,hydrogenProductRepulsion_exact]
  ring

/-- Explicit upper-root condition for the optimized exact-repulsion separator. -/
theorem exactProduct_charge_conditions (Z : ℝ)
    (hZ : (20+5*Real.sqrt 10)/24 < Z) :
    0 < Z ∧ 0 < Z-5/16 ∧ 5*Z^2/8 < (Z-5/16)^2 := by
  have h10p : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have h10s : (Real.sqrt 10)^2 = 10 := Real.sq_sqrt (by norm_num)
  have hleft : 0 < 24*Z-20-5*Real.sqrt 10 := by linarith
  have hright : 0 < 24*Z-20+5*Real.sqrt 10 := by linarith
  refine ⟨by linarith,by linarith,?_⟩
  nlinarith [mul_pos hleft hright]

/-- A normalized, simple physical ground branch with the exact optimized trial bound. -/
theorem exactProduct_ground_branch (Z : ℝ) (hZ : 0 < Z)
    (hα : 0 < Z - 5/16)
    (hsep : 5*Z^2/8 < (Z - 5/16)^2) :
    (variationalGroundEnergy 2 Z).toReal ≤ -(Z - 5/16)^2 ∧
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
  let trial := hydrogenProductTrial Z (Z - 5/16) hα
  have hn := hydrogenProductTrial_norm Z (Z - 5/16) hα
  have hu := (exactProductTrial_energy Z hα).le
  have hstrict : -(Z - 5/16)^2 < -(5*Z^2/8) := by linarith
  obtain ⟨hgap,g,hg,hEg,hcomp,hspec⟩ :=
    twoElectron_ground_branch_of_strict_trial Z hZ trial hn (hu.trans_lt hstrict)
  refine ⟨(coulomb_ground_energy_le_domain_rayleigh 2 Z trial hn).trans hu,
    hgap,g,hg,hEg,?_,hcomp,hspec⟩
  exact fun u hEu => TheoremT.OperatorTheory.ground_complement_eigenspace_rank_one
    (coulombPartialOperator 2 Z) g hg _ _ hEg hgap hcomp u hEu

/-- Every charge above the explicit exact-product threshold has the certified branch. -/
theorem exactProduct_ground_branch_above_threshold (Z : ℝ)
    (hZ : (20+5*Real.sqrt 10)/24 < Z) :
    (variationalGroundEnergy 2 Z).toReal ≤ -(Z - 5/16)^2 ∧
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
  obtain ⟨hZ0,hα,hsep⟩ := exactProduct_charge_conditions Z hZ
  exact exactProduct_ground_branch Z hZ0 hα hsep

/-- Charge 3/2 is separated by the exact moment and fails the prior uncertainty separator. -/
theorem exactProduct_three_halves_ground_energy :
    ¬ (5*(3/2 : ℝ)^2/8 < ((3/2 : ℝ)-Real.sqrt 2/4)^2) ∧
    (variationalGroundEnergy 2 (3/2)).toReal ≤ -(361/256 : ℝ) ∧
    (variationalGroundEnergy 2 (3/2)).toReal < -(45/32 : ℝ) := by
  have hZ0 : 0 < (3/2 : ℝ) := by norm_num
  have hα : 0 < (3/2 : ℝ)-5/16 := by norm_num
  have hsep : 5*(3/2 : ℝ)^2/8 < ((3/2 : ℝ)-5/16)^2 := by norm_num
  have hbranch := exactProduct_ground_branch (3/2) hZ0 hα hsep
  have he : ((3/2 : ℝ)-5/16)^2 = (361/256 : ℝ) := by norm_num
  have hβ : 5*(3/2 : ℝ)^2/8 = (45/32 : ℝ) := by norm_num
  have hE := hbranch.1
  have hgap := hbranch.2.1
  rw [he] at hE
  rw [hβ] at hgap
  refine ⟨?_,hE,hgap⟩
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hl : (31/24 : ℝ) < Real.sqrt 2 := by nlinarith
  nlinarith

#print axioms exactProductTrial_energy
#print axioms exactProduct_charge_conditions
#print axioms exactProduct_ground_branch
#print axioms exactProduct_ground_branch_above_threshold
#print axioms exactProduct_three_halves_ground_energy
end ManyBody.S2