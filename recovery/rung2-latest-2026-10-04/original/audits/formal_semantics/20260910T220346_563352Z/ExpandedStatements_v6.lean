import MixedMultiIndexWord_v1

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
#check @TheoremT.Continuum.mixedMultiIndex
#check @TheoremT.Continuum.mixedMultiIndexWord
#check @TheoremT.Continuum.mixedMultiIndex_sum
#check @TheoremT.Continuum.mixedMultiIndexWord_length
#check @TheoremT.Continuum.mixedMultiIndexWord_count_y
#check @TheoremT.Continuum.mixedMultiIndexWord_count_t
#check @TheoremT.Continuum.coordinateWordCount_cons
#check @TheoremT.Continuum.coordinateMultiIndexWord_add_single_perm
#check @TheoremT.Continuum.mixedMultiIndexWord_add_single_y_perm
#check @TheoremT.Continuum.mixedMultiIndexWord_add_single_t_perm
#check @TheoremT.Continuum.mixedMultiIndexWord_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.mixedMultiIndex
#print axioms TheoremT.Continuum.mixedMultiIndexWord
#print axioms TheoremT.Continuum.mixedMultiIndex_sum
#print axioms TheoremT.Continuum.mixedMultiIndexWord_length
#print axioms TheoremT.Continuum.mixedMultiIndexWord_count_y
#print axioms TheoremT.Continuum.mixedMultiIndexWord_count_t
#print axioms TheoremT.Continuum.coordinateWordCount_cons
#print axioms TheoremT.Continuum.coordinateMultiIndexWord_add_single_perm
#print axioms TheoremT.Continuum.mixedMultiIndexWord_add_single_y_perm
#print axioms TheoremT.Continuum.mixedMultiIndexWord_add_single_t_perm
#print axioms TheoremT.Continuum.mixedMultiIndexWord_zero
