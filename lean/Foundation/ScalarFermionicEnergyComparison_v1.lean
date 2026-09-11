import ScalarCoulombVariational_v1
import HardyGroundNonpositive_v1

/-! The unrestricted scalar ground-energy infimum is a lower bound for the
actual full-spin fermionic infimum. This is a componentwise quadratic bound,
not an assertion that a scalar ground state is fermionic or is attained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators LinearPMap
namespace TheoremT.Continuum

theorem scalar_variational_lower_bound_on_graph (N : ℕ) (Z : ℝ)
    {f h : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f h) :
    (scalarVariationalGroundEnergy N Z).toReal * ‖f‖^2 ≤ (inner ℂ f h).re := by
  have hd := (scalarCoulombOperator_domain_iff N Z f).mpr ⟨h,hg⟩
  let x : (scalarCoulombOperator N Z).domain := ⟨f,hd⟩
  have hx : scalarCoulombOperator N Z x = h :=
    scalar_graph_unique (scalarCoulombOperator_apply_graph N Z x) hg
  have hb := (scalar_variational_isGreatest_operatorLowerBounds N Z).1 x
  change (scalarVariationalGroundEnergy N Z).toReal * ‖f‖^2 ≤
    (inner ℂ f (scalarCoulombOperator N Z x)).re at hb
  rwa [hx] at hb

theorem scalarVariationalGroundEnergy_le_fermionic (N : ℕ) (Z : ℝ) :
    scalarVariationalGroundEnergy N Z ≤ variationalGroundEnergy N Z := by
  have hf := scalar_variational_ground_finite N Z
  have hc := EReal.coe_toReal hf.1 hf.2
  apply le_sInf
  rintro e ⟨ψ,h,hn,hg,rfl⟩
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (SpinConfiguration N)))
    (fun σ _ => scalar_variational_lower_bound_on_graph N Z (hg.2.2 σ))
  rw [← Finset.mul_sum,← PiLp.norm_sq_eq_of_L2,hn,one_pow,mul_one] at hs
  change (scalarVariationalGroundEnergy N Z).toReal ≤ rayleighNumerator ψ h at hs
  rw [← hc]
  exact_mod_cast hs

theorem scalar_variational_ground_nonpositive (N : ℕ) (Z : ℝ) :
    scalarVariationalGroundEnergy N Z ≤ 0 :=
  (scalarVariationalGroundEnergy_le_fermionic N Z).trans (variational_ground_energy_nonpositive N Z)

#print axioms scalar_variational_lower_bound_on_graph
#print axioms scalarVariationalGroundEnergy_le_fermionic
#print axioms scalar_variational_ground_nonpositive
end TheoremT.Continuum
