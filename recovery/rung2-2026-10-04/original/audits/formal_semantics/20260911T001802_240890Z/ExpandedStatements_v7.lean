import WeakFactorialLocalFamilyMatch_v1
import WeakFactorialLocalOuterBound_v1
import WeakFactorialPlateauOuterBound_v1

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
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_ae_local_of_natural_chains
#check @TheoremT.Continuum.WeakGrushin.local_factorial_outer_le_global_weak_representatives
#check @TheoremT.Continuum.WeakGrushin.factorial_local_outer_le_plateau_global
#check @TheoremT.Continuum.WeakGrushin.factorial_local_outer_le_plateau_grushin_output

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_ae_local_of_natural_chains
#print axioms TheoremT.Continuum.WeakGrushin.local_factorial_outer_le_global_weak_representatives
#print axioms TheoremT.Continuum.WeakGrushin.factorial_local_outer_le_plateau_global
#print axioms TheoremT.Continuum.WeakGrushin.factorial_local_outer_le_plateau_grushin_output
