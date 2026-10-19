import MixedPotentialWordProduct_v1
import MixedYEquationSource_v1
import MixedTriangularYGainStep_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct
#check @TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct_nil
#check @TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct_locallyL2
#check @TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct_localY
#check @TheoremT.Continuum.WeakGrushin.mixedYEquationSource
#check @TheoremT.Continuum.WeakGrushin.mixedYEquationSource_locallyL2
#check @TheoremT.Continuum.WeakGrushin.mixedYEquationSource_localY
#check @TheoremT.Continuum.WeakGrushin.mixed_triangular_y_gain_step

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct
#print axioms TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct_nil
#print axioms TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct_locallyL2
#print axioms TheoremT.Continuum.WeakGrushin.mixedPotentialWordProduct_localY
#print axioms TheoremT.Continuum.WeakGrushin.mixedYEquationSource
#print axioms TheoremT.Continuum.WeakGrushin.mixedYEquationSource_locallyL2
#print axioms TheoremT.Continuum.WeakGrushin.mixedYEquationSource_localY
#print axioms TheoremT.Continuum.WeakGrushin.mixed_triangular_y_gain_step
