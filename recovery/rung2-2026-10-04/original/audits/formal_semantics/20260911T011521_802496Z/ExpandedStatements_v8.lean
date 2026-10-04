import FixedBoxSevenGeometry_v1

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
#check @TheoremT.Continuum.WeakGrushin.seven_symm_coordinate
#check @TheoremT.Continuum.WeakGrushin.fixedSevenLower
#check @TheoremT.Continuum.WeakGrushin.fixedSevenUpper
#check @TheoremT.Continuum.WeakGrushin.fixedSevenOpen
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_lower_lt_upper
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_closed_iff
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_open_isOpen
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_open_subset_closed
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_open_image
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_maps_plateau
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_maps_norm_region
#check @TheoremT.Continuum.WeakGrushin.fixedSevenCutoff
#check @TheoremT.Continuum.WeakGrushin.fixedSevenCutoff_data
#check @TheoremT.Continuum.WeakGrushin.fixedSevenEvaluationConstant
#check @TheoremT.Continuum.WeakGrushin.fixedSevenEvaluationConstant_pos
#check @TheoremT.Continuum.WeakGrushin.fixedSeven_evaluation_constant

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.seven_symm_coordinate
#print axioms TheoremT.Continuum.WeakGrushin.fixedSevenLower
#print axioms TheoremT.Continuum.WeakGrushin.fixedSevenUpper
#print axioms TheoremT.Continuum.WeakGrushin.fixedSevenOpen
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_lower_lt_upper
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_closed_iff
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_open_isOpen
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_open_subset_closed
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_open_image
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_maps_plateau
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_maps_norm_region
#print axioms TheoremT.Continuum.WeakGrushin.fixedSevenCutoff
#print axioms TheoremT.Continuum.WeakGrushin.fixedSevenCutoff_data
#print axioms TheoremT.Continuum.WeakGrushin.fixedSevenEvaluationConstant
#print axioms TheoremT.Continuum.WeakGrushin.fixedSevenEvaluationConstant_pos
#print axioms TheoremT.Continuum.WeakGrushin.fixedSeven_evaluation_constant
