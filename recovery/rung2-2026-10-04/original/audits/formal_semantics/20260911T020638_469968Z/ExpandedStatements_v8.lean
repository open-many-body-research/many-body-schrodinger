import RealTaylorCoordinatePolynomial_v1

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
#check @TheoremT.Continuum.realTaylorCoordinatePolynomial
#check @TheoremT.Continuum.realTaylorCoordinatePolynomial_homogeneous
#check @TheoremT.Continuum.realTaylorCoordinatePolynomial_eval
#check @TheoremT.Continuum.polynomialCoeffL1_realTaylorCoordinatePolynomial
#check @TheoremT.Continuum.realTaylorCoordinatePolynomial_hasSum

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.realTaylorCoordinatePolynomial
#print axioms TheoremT.Continuum.realTaylorCoordinatePolynomial_homogeneous
#print axioms TheoremT.Continuum.realTaylorCoordinatePolynomial_eval
#print axioms TheoremT.Continuum.polynomialCoeffL1_realTaylorCoordinatePolynomial
#print axioms TheoremT.Continuum.realTaylorCoordinatePolynomial_hasSum
