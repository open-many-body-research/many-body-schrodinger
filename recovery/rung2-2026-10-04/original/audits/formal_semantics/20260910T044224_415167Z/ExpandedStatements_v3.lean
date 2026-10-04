import HydrogenProductTrialEnergy_v1
import TwoElectronPhysicalGroundBranch_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.hydrogenProductRepulsion
#check @TheoremT.Continuum.hydrogenProductRepulsion_nonneg
#check @TheoremT.Continuum.hydrogenProductRepulsion_sq_le
#check @TheoremT.Continuum.normalizedHydrogen_formValue
#check @TheoremT.Continuum.hydrogenProductTrial_formValue
#check @TheoremT.Continuum.hydrogenProductTrial_energy
#check @TheoremT.Continuum.hydrogenProductTrial_strict
#check @TheoremT.Continuum.twoElectron_physical_ground_branch
#check @TheoremT.Continuum.helium_physical_ground_branch

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.hydrogenProductRepulsion
#print axioms TheoremT.Continuum.hydrogenProductRepulsion_nonneg
#print axioms TheoremT.Continuum.hydrogenProductRepulsion_sq_le
#print axioms TheoremT.Continuum.normalizedHydrogen_formValue
#print axioms TheoremT.Continuum.hydrogenProductTrial_formValue
#print axioms TheoremT.Continuum.hydrogenProductTrial_energy
#print axioms TheoremT.Continuum.hydrogenProductTrial_strict
#print axioms TheoremT.Continuum.twoElectron_physical_ground_branch
#print axioms TheoremT.Continuum.helium_physical_ground_branch
