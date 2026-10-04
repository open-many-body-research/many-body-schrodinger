import WeakGrushinMixedCutoffEquation_v1
import RestrictedL2OutputNorm_v1

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
#check @TheoremT.Continuum.WeakGrushin.mixed_family_local_weakH2
#check @TheoremT.Continuum.WeakGrushin.weak_grushin_mixed_cutoff_equation
#check @TheoremT.Continuum.restrictedL2Extension_norm
#check @TheoremT.Continuum.supported_output_norm_le_restricted
#check @TheoremT.Continuum.restricted_cutoff_output_norm

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.mixed_family_local_weakH2
#print axioms TheoremT.Continuum.WeakGrushin.weak_grushin_mixed_cutoff_equation
#print axioms TheoremT.Continuum.restrictedL2Extension_norm
#print axioms TheoremT.Continuum.supported_output_norm_le_restricted
#print axioms TheoremT.Continuum.restricted_cutoff_output_norm
