import GrushinFactorialLocalProfile_v1
import GrushinFactorialLocalRepresentatives_v1

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
#check @TheoremT.Continuum.WeakGrushin.factorialShiftedWeightedField
#check @TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm
#check @TheoremT.Continuum.WeakGrushin.FactorialLocalMemLp
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile
#check @TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm_nonneg
#check @TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm_le_profile
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile_nonneg
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile_mono_order
#check @TheoremT.Continuum.WeakGrushin.FactorialLocalMemLp.mono_order
#check @TheoremT.Continuum.WeakGrushin.FactorialLocalMemLp.restrict
#check @TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm_mono_domain
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile_mono_domain
#check @TheoremT.Continuum.WeakGrushin.factorial_shifted_outer_norm_eq_local
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile_representatives
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile_unweighted_L2
#check @TheoremT.Continuum.WeakGrushin.factorialLocalProfile_lower_unweighted_L2

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorialShiftedWeightedField
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm
#print axioms TheoremT.Continuum.WeakGrushin.FactorialLocalMemLp
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm_nonneg
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm_le_profile
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile_nonneg
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile_mono_order
#print axioms TheoremT.Continuum.WeakGrushin.FactorialLocalMemLp.mono_order
#print axioms TheoremT.Continuum.WeakGrushin.FactorialLocalMemLp.restrict
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalOuterNorm_mono_domain
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile_mono_domain
#print axioms TheoremT.Continuum.WeakGrushin.factorial_shifted_outer_norm_eq_local
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile_representatives
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile_unweighted_L2
#print axioms TheoremT.Continuum.WeakGrushin.factorialLocalProfile_lower_unweighted_L2
