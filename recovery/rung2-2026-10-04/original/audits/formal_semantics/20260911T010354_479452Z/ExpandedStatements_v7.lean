import FactorialProfilePointwiseWordBudgets_v1
import GrushinActualProfileSmoothRepresentative_v1

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
#check @TheoremT.Continuum.WeakGrushin.factorialOuterIndices_zero_member
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile_unweighted_bound
#check @TheoremT.Continuum.WeakGrushin.factorial_word_cost_le_length_add_four
#check @TheoremT.Continuum.WeakGrushin.factorial_subset_word_cost_le_eleven
#check @TheoremT.Continuum.WeakGrushin.factorial_profile_mixed_subset_word_norms
#check @TheoremT.Continuum.WeakGrushin.factorial_profile_word_memLp
#check @TheoremT.Continuum.WeakGrushin.grushin_actual_profile_smooth_representative

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorialOuterIndices_zero_member
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile_unweighted_bound
#print axioms TheoremT.Continuum.WeakGrushin.factorial_word_cost_le_length_add_four
#print axioms TheoremT.Continuum.WeakGrushin.factorial_subset_word_cost_le_eleven
#print axioms TheoremT.Continuum.WeakGrushin.factorial_profile_mixed_subset_word_norms
#print axioms TheoremT.Continuum.WeakGrushin.factorial_profile_word_memLp
#print axioms TheoremT.Continuum.WeakGrushin.grushin_actual_profile_smooth_representative
