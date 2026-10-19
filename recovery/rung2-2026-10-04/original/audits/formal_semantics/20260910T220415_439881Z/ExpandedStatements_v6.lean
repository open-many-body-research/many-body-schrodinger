import PairKSPotentialAnalytic_v1

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
#check @TheoremT.Continuum.pairKSLift_contDiff_omega
#check @TheoremT.Continuum.pairKSLift_analyticAt
#check @TheoremT.Continuum.pairKSPotential_contDiffAt_omega
#check @TheoremT.Continuum.pairKSPotential_analyticAt
#check @TheoremT.Continuum.pairKSPotential_analyticOnNhd

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.pairKSLift_contDiff_omega
#print axioms TheoremT.Continuum.pairKSLift_analyticAt
#print axioms TheoremT.Continuum.pairKSPotential_contDiffAt_omega
#print axioms TheoremT.Continuum.pairKSPotential_analyticAt
#print axioms TheoremT.Continuum.pairKSPotential_analyticOnNhd
