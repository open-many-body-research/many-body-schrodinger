import PhysicalSpectatorWeakEquationTransport_v1
import CoulombKSPhysicalBoxEquation_v1

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
#check @TheoremT.Continuum.physicalSpectatorReindexAt_measurePreserving
#check @TheoremT.Continuum.physicalSpectatorReindexAt_splitGrushin
#check @TheoremT.Continuum.physicalSpectatorReindexAt_weak_equation
#check @TheoremT.Continuum.scalar_coulomb_nuclear_physical_box_equation
#check @TheoremT.Continuum.scalar_coulomb_pair_physical_box_equation

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_measurePreserving
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_splitGrushin
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_weak_equation
#print axioms TheoremT.Continuum.scalar_coulomb_nuclear_physical_box_equation
#print axioms TheoremT.Continuum.scalar_coulomb_pair_physical_box_equation
