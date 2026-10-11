import RestrictedCompactWeightMemLp_v1

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
#check @TheoremT.Continuum.WeakGrushin.restricted_compact_weight_memLp
#check @TheoremT.Continuum.WeakGrushin.rectangular_continuous_weight_memLp
#check @TheoremT.Continuum.WeakGrushin.rectangular_factorial_monomial_memLp
#check @TheoremT.Continuum.WeakGrushin.regionL2Budget_rectangular_factorial_monomial_memLp

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.restricted_compact_weight_memLp
#print axioms TheoremT.Continuum.WeakGrushin.rectangular_continuous_weight_memLp
#print axioms TheoremT.Continuum.WeakGrushin.rectangular_factorial_monomial_memLp
#print axioms TheoremT.Continuum.WeakGrushin.regionL2Budget_rectangular_factorial_monomial_memLp
