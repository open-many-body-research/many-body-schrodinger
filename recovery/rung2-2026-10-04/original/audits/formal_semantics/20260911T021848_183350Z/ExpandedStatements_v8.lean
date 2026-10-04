import PhysicalKSTaylorCircleInvariance_v1

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
#check @TheoremT.Continuum.physicalKSTaylorPolynomial_invariant_at_center
#check @TheoremT.Continuum.nuclearKSPhysicalTaylorPolynomial_circle_invariant
#check @TheoremT.Continuum.pairKSPhysicalTaylorPolynomial_circle_invariant

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSTaylorPolynomial_invariant_at_center
#print axioms TheoremT.Continuum.nuclearKSPhysicalTaylorPolynomial_circle_invariant
#print axioms TheoremT.Continuum.pairKSPhysicalTaylorPolynomial_circle_invariant
