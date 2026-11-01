import PhysicalSpectatorCutoffTransportAll_v1
import PhysicalSpectatorStepGeometryAll_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoff_test
#check @TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoff_first
#check @TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoff_second
#check @TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_combinedCutoffScalar
#check @TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoffGradientWeight
#check @TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_grushinCutoffWeight
#check @TheoremT.Continuum.WeakGrushin.SpectatorStepGeometry.pullback_physicalSpectatorReindexAt
#check @TheoremT.Continuum.WeakGrushin.physical_h12_spectatorStepGeometryAt

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoff_test
#print axioms TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoff_first
#print axioms TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoff_second
#print axioms TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_combinedCutoffScalar
#print axioms TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_cutoffGradientWeight
#print axioms TheoremT.Continuum.WeakGrushin.physicalSpectatorReindexAt_grushinCutoffWeight
#print axioms TheoremT.Continuum.WeakGrushin.SpectatorStepGeometry.pullback_physicalSpectatorReindexAt
#print axioms TheoremT.Continuum.WeakGrushin.physical_h12_spectatorStepGeometryAt
