import SmoothComplexMixedSourceWords_v1

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
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_contDiffOn
#check @TheoremT.Continuum.WeakGrushin.complex_smooth_local_weak_directional
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_nil
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_contDiffOn
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_locallyL2
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_localY
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_localT_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_contDiffOn
#print axioms TheoremT.Continuum.WeakGrushin.complex_smooth_local_weak_directional
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_nil
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_contDiffOn
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_locallyL2
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_localY
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_localT_zero
