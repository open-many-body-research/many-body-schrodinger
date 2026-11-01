import GrushinActualProfileLocalizedBound_v1
import GrushinActualProfileRecurrence_v1

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
#check @TheoremT.Continuum.WeakGrushin.factorialProfileGraphConstant
#check @TheoremT.Continuum.WeakGrushin.factorialProfileCutoffFirst
#check @TheoremT.Continuum.WeakGrushin.factorialProfileCutoffSecond
#check @TheoremT.Continuum.WeakGrushin.factorial_actual_profile_localized_bound
#check @TheoremT.Continuum.WeakGrushin.factorialProfileRecurrenceConstant
#check @TheoremT.Continuum.WeakGrushin.factorial_actual_profile_recurrence

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorialProfileGraphConstant
#print axioms TheoremT.Continuum.WeakGrushin.factorialProfileCutoffFirst
#print axioms TheoremT.Continuum.WeakGrushin.factorialProfileCutoffSecond
#print axioms TheoremT.Continuum.WeakGrushin.factorial_actual_profile_localized_bound
#print axioms TheoremT.Continuum.WeakGrushin.factorialProfileRecurrenceConstant
#print axioms TheoremT.Continuum.WeakGrushin.factorial_actual_profile_recurrence
