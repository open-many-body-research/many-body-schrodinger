import HomogeneousSpectatorPolynomial_v1

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
#check @TheoremT.Continuum.polynomialCoeffL1_rename_le
#check @TheoremT.Continuum.homogeneousSpectatorPolynomial
#check @TheoremT.Continuum.homogeneousSpectatorPolynomial_eval
#check @TheoremT.Continuum.homogeneousSpectatorPolynomial_isHomogeneous
#check @TheoremT.Continuum.polynomialCoeffL1_homogeneousSpectatorPolynomial

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.polynomialCoeffL1_rename_le
#print axioms TheoremT.Continuum.homogeneousSpectatorPolynomial
#print axioms TheoremT.Continuum.homogeneousSpectatorPolynomial_eval
#print axioms TheoremT.Continuum.homogeneousSpectatorPolynomial_isHomogeneous
#print axioms TheoremT.Continuum.polynomialCoeffL1_homogeneousSpectatorPolynomial
