import CoulombKSPhysicalH12Data_v1
import CoulombKSPhysicalH12_v1
import CoulombKSPhysicalH12MultiIndex_v1

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
#check @TheoremT.Continuum.ksCommonAnnulusVolume
#check @TheoremT.Continuum.ksH12CutoffScalar
#check @TheoremT.Continuum.ksH12CutoffWeight
#check @TheoremT.Continuum.ksH12SpectatorBudget
#check @TheoremT.Continuum.ksH12MixedBudget
#check @TheoremT.Continuum.ksCommonAnnulusVolume_nonneg
#check @TheoremT.Continuum.ksCommonAnnulusVolume_mono
#check @TheoremT.Continuum.ksH12CutoffWeight_nonneg
#check @TheoremT.Continuum.ksH12SpectatorBudget_nonneg
#check @TheoremT.Continuum.ksH12MixedBudget_nonneg
#check @TheoremT.Continuum.ksH12_source_amplitude_bound
#check @TheoremT.Continuum.ksH12_initial_amplitude_bound
#check @TheoremT.Continuum.physicalH12Schedule_zero_subset_commonAnnulus
#check @TheoremT.Continuum.scalar_coulomb_nuclear_zero_physical_coordinate_h12
#check @TheoremT.Continuum.scalar_coulomb_pair_physical_coordinate_h12
#check @TheoremT.Continuum.scalar_coulomb_nuclear_zero_physical_h12_multiindex
#check @TheoremT.Continuum.scalar_coulomb_pair_physical_h12_multiindex

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksCommonAnnulusVolume
#print axioms TheoremT.Continuum.ksH12CutoffScalar
#print axioms TheoremT.Continuum.ksH12CutoffWeight
#print axioms TheoremT.Continuum.ksH12SpectatorBudget
#print axioms TheoremT.Continuum.ksH12MixedBudget
#print axioms TheoremT.Continuum.ksCommonAnnulusVolume_nonneg
#print axioms TheoremT.Continuum.ksCommonAnnulusVolume_mono
#print axioms TheoremT.Continuum.ksH12CutoffWeight_nonneg
#print axioms TheoremT.Continuum.ksH12SpectatorBudget_nonneg
#print axioms TheoremT.Continuum.ksH12MixedBudget_nonneg
#print axioms TheoremT.Continuum.ksH12_source_amplitude_bound
#print axioms TheoremT.Continuum.ksH12_initial_amplitude_bound
#print axioms TheoremT.Continuum.physicalH12Schedule_zero_subset_commonAnnulus
#print axioms TheoremT.Continuum.scalar_coulomb_nuclear_zero_physical_coordinate_h12
#print axioms TheoremT.Continuum.scalar_coulomb_pair_physical_coordinate_h12
#print axioms TheoremT.Continuum.scalar_coulomb_nuclear_zero_physical_h12_multiindex
#print axioms TheoremT.Continuum.scalar_coulomb_pair_physical_h12_multiindex
