import ScalarCoulombOperator_v1
import CoulombSharpSemibounded_v1
import FermionicTrialL2_v2
import SpectralBottom_v2

/-! The normalized scalar Coulomb graph infimum is finite and is exactly the
greatest quadratic lower bound of the actual weak-H² scalar operator. This
module does not assume self-adjointness, a spectral point, or attainment. -/
noncomputable section
open MeasureTheory
open scoped LinearPMap
namespace TheoremT.Continuum

def scalarVariationalGroundEnergy (N : ℕ) (Z : ℝ) : EReal :=
  sInf {e : EReal | ∃ f h : SpatialL2 N,
    ‖f‖ = 1 ∧ scalarHamiltonianGraph N Z f h ∧ e = ((inner ℂ f h).re : EReal)}

theorem scalar_variational_ground_le_trial {N : ℕ} {Z : ℝ} {f h : SpatialL2 N}
    (hn : ‖f‖ = 1) (hg : scalarHamiltonianGraph N Z f h) :
    scalarVariationalGroundEnergy N Z ≤ ((inner ℂ f h).re : EReal) :=
  sInf_le ⟨f,h,hn,hg,rfl⟩

theorem normalized_scalar_graph_nonempty (N : ℕ) (Z : ℝ) :
    ∃ f h : SpatialL2 N, ‖f‖ = 1 ∧ scalarHamiltonianGraph N Z f h := by
  let f₀ := fermionicTrialSpatial N
  let c : ℂ := (‖f₀‖ : ℂ)⁻¹
  let f : SpatialL2 N := c • f₀
  have hn : ‖f‖ = 1 := by
    dsimp [f,c]
    rw [_root_.norm_smul,norm_inv,Complex.norm_real,norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (fermionicTrialSpatial_ne_zero N))]
  have hf : HasH2 f := (fermionicTrialSpatial_hasH2 N).smul c
  obtain ⟨h,hg⟩ := scalar_graph_exists_of_coulombProductL2 hf (coulombProductL2_of_hasH2 Z hf)
  exact ⟨f,h,hn,hg⟩

theorem scalar_variational_ground_sharp_lower_bound (N : ℕ) (Z : ℝ) :
    ((-(N : ℝ)*(max Z 0)^2/2 : ℝ) : EReal) ≤ scalarVariationalGroundEnergy N Z := by
  apply le_sInf
  rintro e ⟨f,h,hn,hg,rfl⟩
  have hb := scalar_graph_sharp_semibounded hg
  rw [hn,one_pow,mul_one] at hb
  rw [spatialL2_real_inner_eq_re] at hb
  exact_mod_cast hb

theorem scalar_variational_ground_finite (N : ℕ) (Z : ℝ) :
    scalarVariationalGroundEnergy N Z ≠ ⊤ ∧ scalarVariationalGroundEnergy N Z ≠ ⊥ := by
  obtain ⟨f,h,hn,hg⟩ := normalized_scalar_graph_nonempty N Z
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) (scalar_variational_ground_le_trial hn hg),
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (scalar_variational_ground_sharp_lower_bound N Z)⟩

theorem scalar_rayleigh_real_smul {N : ℕ} (r : ℝ) (f h : SpatialL2 N) :
    (inner ℂ ((r : ℂ) • f) ((r : ℂ) • h)).re = r^2*(inner ℂ f h).re := by
  rw [inner_smul_left,inner_smul_right]
  simp [Complex.mul_re,pow_two,mul_assoc]

theorem operatorLowerBounds_scalarCoulomb_iff (N : ℕ) (Z a : ℝ) :
    a ∈ TheoremT.OperatorTheory.operatorLowerBounds (scalarCoulombOperator N Z) ↔
      (a : EReal) ≤ scalarVariationalGroundEnergy N Z := by
  constructor
  · intro ha
    apply le_sInf
    rintro e ⟨f,h,hn,hg,rfl⟩
    have hdom : f ∈ (scalarCoulombOperator N Z).domain :=
      (scalarCoulombOperator_domain_iff N Z f).mpr ⟨h,hg⟩
    let x : (scalarCoulombOperator N Z).domain := ⟨f,hdom⟩
    have heq : scalarCoulombOperator N Z x = h :=
      scalar_graph_unique (scalarCoulombOperator_apply_graph N Z x) hg
    have hb := ha x
    change a*‖f‖^2 ≤ (inner ℂ f (scalarCoulombOperator N Z x)).re at hb
    rw [heq,hn,one_pow,mul_one] at hb
    exact_mod_cast hb
  · intro ha x
    let f : SpatialL2 N := x.val
    let h : SpatialL2 N := scalarCoulombOperator N Z x
    have hg : scalarHamiltonianGraph N Z f h := scalarCoulombOperator_apply_graph N Z x
    change a*‖f‖^2 ≤ (inner ℂ f h).re
    by_cases hz : f = 0
    · simp [hz]
    · have hn0 : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      let r : ℝ := ‖f‖⁻¹
      have hn : ‖(r : ℂ) • f‖ = 1 := by
        rw [_root_.norm_smul,Complex.norm_real]
        dsimp [r]
        rw [abs_inv,abs_of_nonneg (norm_nonneg f),inv_mul_cancel₀ hn0]
      have hle := ha.trans (scalar_variational_ground_le_trial hn (scalar_graph_smul (r : ℂ) hg))
      have hr : a ≤ (inner ℂ ((r : ℂ) • f) ((r : ℂ) • h)).re := by exact_mod_cast hle
      rw [scalar_rayleigh_real_smul] at hr
      have hdiv : a ≤ (inner ℂ f h).re/‖f‖^2 := by
        simpa only [r,inv_pow,div_eq_mul_inv,mul_comm] using hr
      exact (le_div_iff₀ (sq_pos_of_ne_zero hn0)).mp hdiv

theorem scalar_variational_isGreatest_operatorLowerBounds (N : ℕ) (Z : ℝ) :
    IsGreatest (TheoremT.OperatorTheory.operatorLowerBounds (scalarCoulombOperator N Z))
      (scalarVariationalGroundEnergy N Z).toReal := by
  have hf := scalar_variational_ground_finite N Z
  have hc := EReal.coe_toReal hf.1 hf.2
  constructor
  · exact (operatorLowerBounds_scalarCoulomb_iff N Z _).mpr hc.le
  · intro a ha
    have hle := (operatorLowerBounds_scalarCoulomb_iff N Z a).mp ha
    rw [← hc] at hle
    exact_mod_cast hle

#print axioms normalized_scalar_graph_nonempty
#print axioms scalar_variational_ground_sharp_lower_bound
#print axioms scalar_variational_ground_finite
#print axioms operatorLowerBounds_scalarCoulomb_iff
#print axioms scalar_variational_isGreatest_operatorLowerBounds
end TheoremT.Continuum
