import GrushinFactorialLowDegreeCases_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
set_option maxRecDepth 16384
set_option pp.rawOnError true
#check @TheoremT.Continuum.WeakGrushin.finite_multiindex_eq_zero_of_sum_eq_zero
#check @TheoremT.Continuum.WeakGrushin.finite_multiindex_single_of_sum_eq_one
#check @TheoremT.Continuum.WeakGrushin.finite_multiindex_two_singles_of_sum_eq_two
#check @TheoremT.Continuum.WeakGrushin.finite_multiindex_degree_le_two_cases
#check @TheoremT.Continuum.WeakGrushin.factorial_outer_derivative_six_cases

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.finite_multiindex_eq_zero_of_sum_eq_zero
#print axioms TheoremT.Continuum.WeakGrushin.finite_multiindex_single_of_sum_eq_one
#print axioms TheoremT.Continuum.WeakGrushin.finite_multiindex_two_singles_of_sum_eq_two
#print axioms TheoremT.Continuum.WeakGrushin.finite_multiindex_degree_le_two_cases
#print axioms TheoremT.Continuum.WeakGrushin.factorial_outer_derivative_six_cases
