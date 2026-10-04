import FactorialMonomialBudgetBound_v1
import FactorialProfileFiniteBudgetBound_v1
import FactorialR9BaseProfile_v1

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
#check @TheoremT.Continuum.WeakGrushin.factorial_monomial_region_budget_bound
#check @TheoremT.Continuum.WeakGrushin.factorial_shifted_total_le_of_cost
#check @TheoremT.Continuum.WeakGrushin.factorial_profile_bound_of_region_budgets
#check @TheoremT.Continuum.WeakGrushin.factorial_profile_bound_on_subregion_of_budgets
#check @TheoremT.Continuum.WeakGrushin.factorial_profile_bound_of_weak_finite_budget
#check @TheoremT.Continuum.WeakGrushin.factorial_R9_base_profile_of_H12

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorial_monomial_region_budget_bound
#print axioms TheoremT.Continuum.WeakGrushin.factorial_shifted_total_le_of_cost
#print axioms TheoremT.Continuum.WeakGrushin.factorial_profile_bound_of_region_budgets
#print axioms TheoremT.Continuum.WeakGrushin.factorial_profile_bound_on_subregion_of_budgets
#print axioms TheoremT.Continuum.WeakGrushin.factorial_profile_bound_of_weak_finite_budget
#print axioms TheoremT.Continuum.WeakGrushin.factorial_R9_base_profile_of_H12
