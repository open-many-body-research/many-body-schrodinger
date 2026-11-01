import IteratedFDerivScalarLinearCompositionAt_v1
import RealCoordinateEmbedding_v1
import RealRestrictionIteratedDerivativeWord_v1

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
#check @TheoremT.Continuum.iteratedFDeriv_comp_right_of_contDiffAt_scalar
#check @TheoremT.Continuum.realCoordinateEmbedding
#check @TheoremT.Continuum.realCoordinateEmbedding_coe
#check @TheoremT.Continuum.realCoordinateEmbedding_single
#check @TheoremT.Continuum.real_restriction_contDiffAt
#check @TheoremT.Continuum.real_restriction_iteratedFDeriv_word

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.iteratedFDeriv_comp_right_of_contDiffAt_scalar
#print axioms TheoremT.Continuum.realCoordinateEmbedding
#print axioms TheoremT.Continuum.realCoordinateEmbedding_coe
#print axioms TheoremT.Continuum.realCoordinateEmbedding_single
#print axioms TheoremT.Continuum.real_restriction_contDiffAt
#print axioms TheoremT.Continuum.real_restriction_iteratedFDeriv_word
