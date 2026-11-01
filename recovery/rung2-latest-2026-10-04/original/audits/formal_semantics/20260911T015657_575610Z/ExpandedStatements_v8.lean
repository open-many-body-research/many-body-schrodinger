import CoordinateWordMultilinear_v1
import HomogeneousPolynomialMultilinear_v1

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
#check @TheoremT.Continuum.coordinateWordMultilinear
#check @TheoremT.Continuum.coordinateWordMultilinear_apply
#check @TheoremT.Continuum.coordinateWordMultilinear_norm_le
#check @TheoremT.Continuum.coordinateWordMultilinear_diagonal
#check @TheoremT.Continuum.homogeneous_polynomial_multilinear_exists

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.coordinateWordMultilinear
#print axioms TheoremT.Continuum.coordinateWordMultilinear_apply
#print axioms TheoremT.Continuum.coordinateWordMultilinear_norm_le
#print axioms TheoremT.Continuum.coordinateWordMultilinear_diagonal
#print axioms TheoremT.Continuum.homogeneous_polynomial_multilinear_exists
