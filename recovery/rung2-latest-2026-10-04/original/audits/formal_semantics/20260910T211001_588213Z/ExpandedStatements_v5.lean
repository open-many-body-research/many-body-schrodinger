import PhysicalSpectatorReindexAll_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.twoElectronSpectatorCoordinateEquiv
#check @TheoremT.Continuum.twoElectronSpectatorPositionEquiv
#check @TheoremT.Continuum.twoElectronSpectatorPositionEquiv_apply
#check @TheoremT.Continuum.twoElectronSpectatorPositionEquiv_symm_apply
#check @TheoremT.Continuum.twoElectronSpectatorPositionEquiv_basis
#check @TheoremT.Continuum.twoElectronSpectatorCoordinate_card
#check @TheoremT.Continuum.physicalSpectatorReindexAt
#check @TheoremT.Continuum.physicalSpectatorReindexAt_apply
#check @TheoremT.Continuum.physicalSpectatorReindexAt_symm_apply
#check @TheoremT.Continuum.physicalSpectatorReindexAt_yDir
#check @TheoremT.Continuum.physicalSpectatorReindexAt_tDir
#check @TheoremT.Continuum.physicalSpectatorReindexAt_symm_yDir
#check @TheoremT.Continuum.physicalSpectatorReindexAt_symm_tDir
#check @TheoremT.Continuum.physicalSpectatorReindexAt_contDiff
#check @TheoremT.Continuum.physicalSpectatorReindexAt_symm_contDiff
#check @TheoremT.Continuum.physicalSpectatorHomeomorphAt
#check @TheoremT.Continuum.physicalSpectatorHomeomorphAt_apply
#check @TheoremT.Continuum.physicalSpectatorHomeomorphAt_symm_apply
#check @TheoremT.Continuum.twoElectronSpectatorPositionEquiv_zero
#check @TheoremT.Continuum.physicalSpectatorReindexAt_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.twoElectronSpectatorCoordinateEquiv
#print axioms TheoremT.Continuum.twoElectronSpectatorPositionEquiv
#print axioms TheoremT.Continuum.twoElectronSpectatorPositionEquiv_apply
#print axioms TheoremT.Continuum.twoElectronSpectatorPositionEquiv_symm_apply
#print axioms TheoremT.Continuum.twoElectronSpectatorPositionEquiv_basis
#print axioms TheoremT.Continuum.twoElectronSpectatorCoordinate_card
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_apply
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_symm_apply
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_yDir
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_tDir
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_symm_yDir
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_symm_tDir
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_contDiff
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_symm_contDiff
#print axioms TheoremT.Continuum.physicalSpectatorHomeomorphAt
#print axioms TheoremT.Continuum.physicalSpectatorHomeomorphAt_apply
#print axioms TheoremT.Continuum.physicalSpectatorHomeomorphAt_symm_apply
#print axioms TheoremT.Continuum.twoElectronSpectatorPositionEquiv_zero
#print axioms TheoremT.Continuum.physicalSpectatorReindexAt_zero
