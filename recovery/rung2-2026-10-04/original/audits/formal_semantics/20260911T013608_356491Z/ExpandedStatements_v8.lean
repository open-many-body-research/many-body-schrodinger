import FiniteHomogeneousMonomialCount_v1

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
#check @TheoremT.Continuum.degreeMonomialExponents4
#check @TheoremT.Continuum.mem_degreeMonomialExponents4_iff_sum
#check @TheoremT.Continuum.mem_degreeMonomialExponents4_iff_finsupp_sum
#check @TheoremT.Continuum.card_degreeMonomialExponents4_eq_choose
#check @TheoremT.Continuum.card_degreeMonomialExponents4_le_pow
#check @TheoremT.Continuum.card_degreeMonomialExponents4_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.degreeMonomialExponents4
#print axioms TheoremT.Continuum.mem_degreeMonomialExponents4_iff_sum
#print axioms TheoremT.Continuum.mem_degreeMonomialExponents4_iff_finsupp_sum
#print axioms TheoremT.Continuum.card_degreeMonomialExponents4_eq_choose
#print axioms TheoremT.Continuum.card_degreeMonomialExponents4_le_pow
#print axioms TheoremT.Continuum.card_degreeMonomialExponents4_zero
