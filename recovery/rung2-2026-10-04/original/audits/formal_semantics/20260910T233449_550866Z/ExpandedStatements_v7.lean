import ProductWeakJetClosedSupport_v1
import WeakGrushinRadialJetBounds_v1
import WeakGrushinRadialOutput_v1

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
#check @TheoremT.Continuum.weakProductL2Directional_closed_support
#check @TheoremT.Continuum.weakProductL2Second_closed_support
#check @TheoremT.Continuum.WeakGrushin.smooth_radial_jet_bounds
#check @TheoremT.Continuum.WeakGrushin.compact_weakH2_radial_estimates
#check @TheoremT.Continuum.WeakGrushin.compact_weakH2_weighted_jet_memLp
#check @TheoremT.Continuum.WeakGrushin.compact_weakH2_radial_output_estimates

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.weakProductL2Directional_closed_support
#print axioms TheoremT.Continuum.weakProductL2Second_closed_support
#print axioms TheoremT.Continuum.WeakGrushin.smooth_radial_jet_bounds
#print axioms TheoremT.Continuum.WeakGrushin.compact_weakH2_radial_estimates
#print axioms TheoremT.Continuum.WeakGrushin.compact_weakH2_weighted_jet_memLp
#print axioms TheoremT.Continuum.WeakGrushin.compact_weakH2_radial_output_estimates
