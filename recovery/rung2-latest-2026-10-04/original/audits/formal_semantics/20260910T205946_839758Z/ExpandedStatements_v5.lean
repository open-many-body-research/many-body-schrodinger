import PhysicalSpectatorReindex_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.physicalSpectatorReindex
#check @TheoremT.Continuum.physicalSpectatorReindex_apply
#check @TheoremT.Continuum.physicalSpectatorReindex_symm_apply
#check @TheoremT.Continuum.physicalSpectatorReindex_yDir
#check @TheoremT.Continuum.physicalSpectatorReindex_tDir
#check @TheoremT.Continuum.physicalSpectatorReindex_symm_yDir
#check @TheoremT.Continuum.physicalSpectatorReindex_symm_tDir
#check @TheoremT.Continuum.physicalSpectatorCoordinate_card
#check @TheoremT.Continuum.physicalSpectatorReindex_contDiff
#check @TheoremT.Continuum.physicalSpectatorReindex_symm_contDiff
#check @TheoremT.Continuum.physicalSpectatorHomeomorph
#check @TheoremT.Continuum.physicalSpectatorHomeomorph_apply
#check @TheoremT.Continuum.physicalSpectatorHomeomorph_symm_apply

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalSpectatorReindex
#print axioms TheoremT.Continuum.physicalSpectatorReindex_apply
#print axioms TheoremT.Continuum.physicalSpectatorReindex_symm_apply
#print axioms TheoremT.Continuum.physicalSpectatorReindex_yDir
#print axioms TheoremT.Continuum.physicalSpectatorReindex_tDir
#print axioms TheoremT.Continuum.physicalSpectatorReindex_symm_yDir
#print axioms TheoremT.Continuum.physicalSpectatorReindex_symm_tDir
#print axioms TheoremT.Continuum.physicalSpectatorCoordinate_card
#print axioms TheoremT.Continuum.physicalSpectatorReindex_contDiff
#print axioms TheoremT.Continuum.physicalSpectatorReindex_symm_contDiff
#print axioms TheoremT.Continuum.physicalSpectatorHomeomorph
#print axioms TheoremT.Continuum.physicalSpectatorHomeomorph_apply
#print axioms TheoremT.Continuum.physicalSpectatorHomeomorph_symm_apply
