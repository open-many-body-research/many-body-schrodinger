import SpectatorTotalDegreeIndices_v1
import GroupedHomogeneousSpectatorPolynomial_v1
import GroupedHomogeneousSpectatorAnalytic_v1

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
#check @TheoremT.Continuum.spectatorTotalDegreeIndices
#check @TheoremT.Continuum.mem_spectatorTotalDegreeIndices_iff
#check @TheoremT.Continuum.card_spectatorTotalDegreeIndices
#check @TheoremT.Continuum.groupedHomogeneousSpectatorPolynomial
#check @TheoremT.Continuum.groupedHomogeneousSpectatorPolynomial_isHomogeneous
#check @TheoremT.Continuum.polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial
#check @TheoremT.Continuum.grouped_homogeneous_spectator_series_analytic

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.spectatorTotalDegreeIndices
#print axioms TheoremT.Continuum.mem_spectatorTotalDegreeIndices_iff
#print axioms TheoremT.Continuum.card_spectatorTotalDegreeIndices
#print axioms TheoremT.Continuum.groupedHomogeneousSpectatorPolynomial
#print axioms TheoremT.Continuum.groupedHomogeneousSpectatorPolynomial_isHomogeneous
#print axioms TheoremT.Continuum.polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial
#print axioms TheoremT.Continuum.grouped_homogeneous_spectator_series_analytic
