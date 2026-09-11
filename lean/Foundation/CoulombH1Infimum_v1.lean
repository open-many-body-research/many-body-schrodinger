import CoulombH1Continuity_v1
import CoulombH1GraphEnergy_v1
import HardyFermionicH1Density_v1
import VariationalOperatorBridge_v2

/-! The actual H¹ form infimum equals the original H² graph variational
infimum. This extension uses proved fermionic H² density in the weak H¹ graph
norm, with no binding, gap, ground-vector or attainment assumption. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology LinearPMap

namespace TheoremT.Continuum

def coulombH1LowerBounds (N : ℕ) (Z : ℝ) : Set ℝ :=
  {a | ∀ ψ q, coulombH1FormValue N Z ψ q → a * ‖ψ‖^2 ≤ q}

theorem operatorLowerBound_on_graph {N : ℕ} {Z a : ℝ}
    (ha : a ∈ TheoremT.OperatorTheory.operatorLowerBounds (coulombPartialOperator N Z))
    {ψ h : SpinSpace N} (hg : hamiltonianGraph N Z ψ h) :
    a * ‖ψ‖^2 ≤ rayleighNumerator ψ h := by
  let ψF : FermionicSpace N := ⟨ψ, hg.1⟩
  let hF : FermionicSpace N := ⟨h, hg.2.1⟩
  have hdom : ψF ∈ (coulombPartialOperator N Z).domain :=
    (coulombPartialOperator_domain_iff N Z ψF).mpr ⟨hF, hg⟩
  let x : (coulombPartialOperator N Z).domain := ⟨ψF, hdom⟩
  have heq : (coulombPartialOperator N Z x).val = h :=
    hamiltonian_graph_unique (coulombPartialOperator_apply_graph N Z x) hg
  have hb := ha x
  change a * ‖ψ‖^2 ≤ (inner ℂ ψ (coulombPartialOperator N Z x).val).re at hb
  rwa [heq, ← rayleighNumerator_eq_re_complex_inner] at hb

theorem operatorLowerBound_on_h1Form {N : ℕ} {Z a : ℝ}
    (ha : a ∈ TheoremT.OperatorTheory.operatorLowerBounds (coulombPartialOperator N Z)) :
    a ∈ coulombH1LowerBounds N Z := by
  rintro ψ q ⟨hψ, d, v, hd, hv, rfl⟩
  obtain ⟨ψn, dn, hdom, hdn, hψt, hdt⟩ :=
    fermionic_h1_approx_by_h2_sequence hψ d hd
  have hvex (n : ℕ) := spin_coulomb_product_exists_of_hasH1 Z (ψn n)
    (fun σ => h2_implies_h1 ((hdom n).2 σ))
  choose vn hvn using hvex
  have hE := coulombH1Energy_tendsto Z ψn ψ dn d vn v hdn hd hvn hv hψt hdt
  have hn := (hψt.norm.pow 2).const_mul a
  apply le_of_tendsto_of_tendsto' hn hE
  intro n
  obtain ⟨hn, hgn⟩ := (hamiltonian_graph_existsUnique_of_targetDomain (Z := Z)
    (hdom n)).exists
  have hform : coulombH1FormValue N Z (ψn n) (coulombH1Energy (ψn n) (dn n) (vn n)) :=
    ⟨(hdom n).1, dn n, vn n, hdn n, hvn n, rfl⟩
  rw [coulombH1FormValue_eq_graph_energy hform hgn]
  exact operatorLowerBound_on_graph ha hgn

theorem coulombH1LowerBounds_eq_operatorLowerBounds (N : ℕ) (Z : ℝ) :
    coulombH1LowerBounds N Z =
      TheoremT.OperatorTheory.operatorLowerBounds (coulombPartialOperator N Z) := by
  ext a
  constructor
  · intro ha x
    have hg := coulombPartialOperator_apply_graph N Z x
    have hb := ha x.val.val (rayleighNumerator x.val.val
      ((coulombPartialOperator N Z) x).val) (hamiltonian_graph_formValue hg)
    rwa [rayleighNumerator_eq_re_complex_inner] at hb
  · exact operatorLowerBound_on_h1Form

/-- Exact equality of the two normalized continuum energy definitions.
The left side ranges over the actual weak H¹ fermionic domain; the right side
is the unchanged original Hamiltonian-graph definition on weak H². -/
theorem formGroundEnergy_eq_variationalGroundEnergy (N : ℕ) (Z : ℝ) :
    formGroundEnergy N Z = variationalGroundEnergy N Z := by
  apply le_antisymm (form_ground_le_variational N Z)
  apply le_sInf
  rintro E ⟨ψ, q, hn, hq, rfl⟩
  have ha := (variational_energy_isGreatest_operatorLowerBounds N Z).1
  have hb := operatorLowerBound_on_h1Form ha ψ q hq
  rw [hn, one_pow, mul_one] at hb
  have hfinite := variational_ground_energy_finite N Z
  have hc := EReal.coe_toReal hfinite.1 hfinite.2
  rw [← hc]
  exact_mod_cast hb

#print axioms operatorLowerBound_on_h1Form
#print axioms coulombH1LowerBounds_eq_operatorLowerBounds
#print axioms formGroundEnergy_eq_variationalGroundEnergy

end TheoremT.Continuum
