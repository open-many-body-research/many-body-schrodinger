import GrushinFiniteStepGeometry_v1
import GrushinFiniteNestedGeometry_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinRegion
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinMiddle
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinInnerCutoff
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinEnergyCutoff
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_isOpen
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_measurableSet
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_zero
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_antitone
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_subset_initial
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_contains_closed
#check @TheoremT.Continuum.WeakGrushin.finite_grushin_step_geometry
#check @TheoremT.Continuum.WeakGrushin.finite_grushin_nested_geometry
#check @TheoremT.Continuum.WeakGrushin.finite_grushin_nested_final_contains
#check @TheoremT.Continuum.WeakGrushin.finite_grushin_nested_domains

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinRegion
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinMiddle
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinInnerCutoff
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinEnergyCutoff
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_isOpen
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_measurableSet
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_zero
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_antitone
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_subset_initial
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinRegion_contains_closed
#print axioms TheoremT.Continuum.WeakGrushin.finite_grushin_step_geometry
#print axioms TheoremT.Continuum.WeakGrushin.finite_grushin_nested_geometry
#print axioms TheoremT.Continuum.WeakGrushin.finite_grushin_nested_final_contains
#print axioms TheoremT.Continuum.WeakGrushin.finite_grushin_nested_domains
