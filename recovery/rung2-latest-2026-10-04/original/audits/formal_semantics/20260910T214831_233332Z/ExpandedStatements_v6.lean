import SmoothComplexMixedSourceBounds_v1

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
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_eq_iteratedFDeriv
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_norm_le_iteratedFDeriv
#check @TheoremT.Continuum.WeakGrushin.complexCoordinateWordDeriv_of_tWord
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_eq_coordinateWord
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_norm_le_iteratedFDeriv
#check @TheoremT.Continuum.WeakGrushin.mixedWordDeriv_compact_finite_bound
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_compact_finite_bound
#check @TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_compact_region_budgets

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_eq_iteratedFDeriv
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_norm_le_iteratedFDeriv
#print axioms TheoremT.Continuum.WeakGrushin.complexCoordinateWordDeriv_of_tWord
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_eq_coordinateWord
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_norm_le_iteratedFDeriv
#print axioms TheoremT.Continuum.WeakGrushin.mixedWordDeriv_compact_finite_bound
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_compact_finite_bound
#print axioms TheoremT.Continuum.WeakGrushin.complexMixedSourceWord_compact_region_budgets
