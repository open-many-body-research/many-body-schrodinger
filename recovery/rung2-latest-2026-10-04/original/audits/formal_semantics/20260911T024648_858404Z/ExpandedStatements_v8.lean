import PhysicalKSTaylorAnalyticDescentData_v1

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
#check @TheoremT.Continuum.physicalKSTaylorEvenSpectatorFamily
#check @TheoremT.Continuum.physicalKSAnalyticDescentA
#check @TheoremT.Continuum.physicalKSAnalyticDescentB
#check @TheoremT.Continuum.physicalKSTaylorEvenSpectatorFamily_homogeneous
#check @TheoremT.Continuum.physicalKSTaylorEvenSpectatorFamily_coeff_bound
#check @TheoremT.Continuum.physicalKSAnalyticDescent_analytic_of_balanced
#check @TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_analytic
#check @TheoremT.Continuum.pairKSPhysicalAnalyticDescent_analytic

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSTaylorEvenSpectatorFamily
#print axioms TheoremT.Continuum.physicalKSAnalyticDescentA
#print axioms TheoremT.Continuum.physicalKSAnalyticDescentB
#print axioms TheoremT.Continuum.physicalKSTaylorEvenSpectatorFamily_homogeneous
#print axioms TheoremT.Continuum.physicalKSTaylorEvenSpectatorFamily_coeff_bound
#print axioms TheoremT.Continuum.physicalKSAnalyticDescent_analytic_of_balanced
#print axioms TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_analytic
#print axioms TheoremT.Continuum.pairKSPhysicalAnalyticDescent_analytic
