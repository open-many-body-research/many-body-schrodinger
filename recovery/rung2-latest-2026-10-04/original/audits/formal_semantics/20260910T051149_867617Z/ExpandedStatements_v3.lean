import PhysicalSpinSinglet_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.spinSingletLift
#check @TheoremT.Continuum.spinSingletLift_apply
#check @TheoremT.Continuum.spinSingletLift_weight
#check @TheoremT.Continuum.spinSingletLift_smul
#check @TheoremT.Continuum.spinSingletLift_fermionic
#check @TheoremT.Continuum.spinSingletLift_graph
#check @TheoremT.Continuum.spinSingletLift_inner
#check @TheoremT.Continuum.spinSingletLift_norm_sq
#check @TheoremT.Continuum.spinSingletDifference
#check @TheoremT.Continuum.spinSingletDifference_swap
#check @TheoremT.Continuum.spinSingletDifference_graph
#check @TheoremT.Continuum.spinSingletDifference_smul

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.spinSingletLift
#print axioms TheoremT.Continuum.spinSingletLift_apply
#print axioms TheoremT.Continuum.spinSingletLift_weight
#print axioms TheoremT.Continuum.spinSingletLift_smul
#print axioms TheoremT.Continuum.spinSingletLift_fermionic
#print axioms TheoremT.Continuum.spinSingletLift_graph
#print axioms TheoremT.Continuum.spinSingletLift_inner
#print axioms TheoremT.Continuum.spinSingletLift_norm_sq
#print axioms TheoremT.Continuum.spinSingletDifference
#print axioms TheoremT.Continuum.spinSingletDifference_swap
#print axioms TheoremT.Continuum.spinSingletDifference_graph
#print axioms TheoremT.Continuum.spinSingletDifference_smul
