import PowerSeriesUniformTranslationBound_v1
import KSScaledFactorialWordBounds_v1

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
#check @TheoremT.Continuum.powerSeriesTranslationMajorant
#check @TheoremT.Continuum.powerSeries_changeOrigin_uniform_nnnorm
#check @TheoremT.Continuum.powerSeries_changeOrigin_uniform_norm
#check @TheoremT.Continuum.powerSeries_changeOrigin_uniform_geometric_bound
#check @TheoremT.Continuum.nuclearKS_uniform_factorial_word_bounds
#check @TheoremT.Continuum.pairKS_uniform_factorial_word_bounds

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.powerSeriesTranslationMajorant
#print axioms TheoremT.Continuum.powerSeries_changeOrigin_uniform_nnnorm
#print axioms TheoremT.Continuum.powerSeries_changeOrigin_uniform_norm
#print axioms TheoremT.Continuum.powerSeries_changeOrigin_uniform_geometric_bound
#print axioms TheoremT.Continuum.nuclearKS_uniform_factorial_word_bounds
#print axioms TheoremT.Continuum.pairKS_uniform_factorial_word_bounds
