import ScalarCoulombFormLowerBounds_v1
import ScalarCoulombVariational_v1

/-! Equality of normalized infima for the actual scalar weak-H¹ form and
the actual scalar weak-H² operator graph. No attainment is assumed. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_form_ground_le_variational (N : ℕ) (Z : ℝ) :
    scalarFormGroundEnergy N Z ≤ scalarVariationalGroundEnergy N Z := by
  apply le_sInf
  rintro E ⟨f,h,hn,hg,rfl⟩
  exact sInf_le ⟨f,(inner ℂ f h).re,hn,scalarHamiltonianGraph_formValue hg,rfl⟩

theorem scalarFormGroundEnergy_eq_variationalGroundEnergy (N : ℕ) (Z : ℝ) :
    scalarFormGroundEnergy N Z = scalarVariationalGroundEnergy N Z := by
  apply le_antisymm (scalar_form_ground_le_variational N Z)
  apply le_sInf
  rintro E ⟨f,q,hn,hq,rfl⟩
  have ha := (scalar_variational_isGreatest_operatorLowerBounds N Z).1
  have hb := scalar_operatorLowerBound_on_h1Form ha f q hq
  rw [hn,one_pow,mul_one] at hb
  have hf := scalar_variational_ground_finite N Z
  have hc := EReal.coe_toReal hf.1 hf.2
  rw [← hc]
  exact_mod_cast hb

theorem scalar_form_ground_finite (N : ℕ) (Z : ℝ) :
    scalarFormGroundEnergy N Z ≠ ⊤ ∧ scalarFormGroundEnergy N Z ≠ ⊥ := by
  rw [scalarFormGroundEnergy_eq_variationalGroundEnergy]
  exact scalar_variational_ground_finite N Z

theorem scalarFormGroundEnergy_le_normalized_form {N : ℕ} {Z : ℝ}
    {f : SpatialL2 N} {q : ℝ} (hn : ‖f‖ = 1)
    (hq : scalarCoulombH1FormValue N Z f q) :
    scalarFormGroundEnergy N Z ≤ (q : EReal) :=
  sInf_le ⟨f,q,hn,hq,rfl⟩

theorem scalar_form_ground_sharp_lower_bound (N : ℕ) (Z : ℝ) :
    ((-(N : ℝ) * (max Z 0)^2 / 2 : ℝ) : EReal) ≤ scalarFormGroundEnergy N Z := by
  rw [scalarFormGroundEnergy_eq_variationalGroundEnergy]
  exact scalar_variational_ground_sharp_lower_bound N Z

#print axioms scalarFormGroundEnergy_eq_variationalGroundEnergy
#print axioms scalar_form_ground_finite
#print axioms scalar_form_ground_sharp_lower_bound
end TheoremT.Continuum
