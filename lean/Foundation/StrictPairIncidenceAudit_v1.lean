import StrictPairIncidence_v1

/-! Independent semantic restatement of the actual strict-pair incidence
identity, with the pair subtype expanded. No nonnegativity or N > 0 is assumed. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem audit_strict_pair_incidence (N : ℕ) (a : Fin N → ℝ) :
    (∑ q : {q : Fin N × Fin N // q.1 < q.2}, (a q.val.1 + a q.val.2)) =
      ((N : ℝ) - 1) * ∑ i : Fin N, a i :=
  strictElectronPair_incidence_sum N a

set_option pp.explicit true in
set_option pp.universes true in
#check audit_strict_pair_incidence

#print StrictElectronPair
#print axioms strictElectronPair_sum_real
#print axioms strictElectronPair_incidence_sum
#print axioms audit_strict_pair_incidence

end TheoremT.Continuum
