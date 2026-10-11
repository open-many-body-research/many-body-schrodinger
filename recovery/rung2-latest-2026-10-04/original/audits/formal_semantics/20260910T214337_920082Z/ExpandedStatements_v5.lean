import GrushinFiniteBoxGap_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_pos
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_scaled
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_y_margin
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_t_margin
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_y_strict
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_t_strict
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_consumed_nonneg
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_y_consumed_le
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_t_consumed_le
#check @TheoremT.Continuum.WeakGrushin.finiteGrushinGap_consumed_bounds

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_pos
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_scaled
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_y_margin
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_t_margin
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_y_strict
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_t_strict
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_consumed_nonneg
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_y_consumed_le
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_t_consumed_le
#print axioms TheoremT.Continuum.WeakGrushin.finiteGrushinGap_consumed_bounds
