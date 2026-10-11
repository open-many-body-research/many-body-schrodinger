import CoulombKSPhysicalH12DataAll_v1
import CoulombKSPhysicalH12All_v1
import CoulombKSPhysicalH12MultiIndexAll_v1

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
#check @TheoremT.Continuum.ksCommonAnnulusVolumeAt
#check @TheoremT.Continuum.ksH12SpectatorBudgetAt
#check @TheoremT.Continuum.ksH12MixedBudgetAt
#check @TheoremT.Continuum.ksCommonAnnulusVolumeAt_nonneg
#check @TheoremT.Continuum.ksCommonAnnulusVolumeAt_mono
#check @TheoremT.Continuum.ksH12SpectatorBudgetAt_nonneg
#check @TheoremT.Continuum.ksH12MixedBudgetAt_nonneg
#check @TheoremT.Continuum.ksH12_source_amplitude_bound_at
#check @TheoremT.Continuum.ksH12_initial_amplitude_bound_at
#check @TheoremT.Continuum.physicalH12Schedule_subset_commonAnnulusAt
#check @TheoremT.Continuum.scalar_coulomb_nuclear_physical_coordinate_h12
#check @TheoremT.Continuum.scalar_coulomb_nuclear_physical_h12_multiindex

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksCommonAnnulusVolumeAt
#print axioms TheoremT.Continuum.ksH12SpectatorBudgetAt
#print axioms TheoremT.Continuum.ksH12MixedBudgetAt
#print axioms TheoremT.Continuum.ksCommonAnnulusVolumeAt_nonneg
#print axioms TheoremT.Continuum.ksCommonAnnulusVolumeAt_mono
#print axioms TheoremT.Continuum.ksH12SpectatorBudgetAt_nonneg
#print axioms TheoremT.Continuum.ksH12MixedBudgetAt_nonneg
#print axioms TheoremT.Continuum.ksH12_source_amplitude_bound_at
#print axioms TheoremT.Continuum.ksH12_initial_amplitude_bound_at
#print axioms TheoremT.Continuum.physicalH12Schedule_subset_commonAnnulusAt
#print axioms TheoremT.Continuum.scalar_coulomb_nuclear_physical_coordinate_h12
#print axioms TheoremT.Continuum.scalar_coulomb_nuclear_physical_h12_multiindex
