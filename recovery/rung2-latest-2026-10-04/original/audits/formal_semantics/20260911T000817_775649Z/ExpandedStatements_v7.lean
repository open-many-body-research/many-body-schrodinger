import GrushinFactorialBoxProfile_v1
import LocalWeakGrushinActualProfile_v1

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
#check @TheoremT.Continuum.WeakGrushin.factorialProfileBox
#check @TheoremT.Continuum.WeakGrushin.factorialBoxProfile
#check @TheoremT.Continuum.WeakGrushin.factorialProfileBox_antitone
#check @TheoremT.Continuum.WeakGrushin.factorial_shifted_total_le
#check @TheoremT.Continuum.WeakGrushin.factorialLocalMemLp_rectangular
#check @TheoremT.Continuum.WeakGrushin.factorialProfileBox_memLp_of_all_finite_budgets
#check @TheoremT.Continuum.WeakGrushin.factorialBoxProfile_nonneg
#check @TheoremT.Continuum.WeakGrushin.factorialBoxProfile_antitone_of_all_finite_budgets
#check @TheoremT.Continuum.WeakGrushin.local_smooth_weak_grushin_actual_box_profile

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorialProfileBox
#print axioms TheoremT.Continuum.WeakGrushin.factorialBoxProfile
#print axioms TheoremT.Continuum.WeakGrushin.factorialProfileBox_antitone
#print axioms TheoremT.Continuum.WeakGrushin.factorial_shifted_total_le
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalMemLp_rectangular
#print axioms TheoremT.Continuum.WeakGrushin.factorialProfileBox_memLp_of_all_finite_budgets
#print axioms TheoremT.Continuum.WeakGrushin.factorialBoxProfile_nonneg
#print axioms TheoremT.Continuum.WeakGrushin.factorialBoxProfile_antitone_of_all_finite_budgets
#print axioms TheoremT.Continuum.WeakGrushin.local_smooth_weak_grushin_actual_box_profile
