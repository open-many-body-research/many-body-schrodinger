import CompactWeakGrushinEnergy_v1

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
#check @TheoremT.Continuum.WeakGrushin.weakGrushinGradientEnergy
#check @TheoremT.Continuum.WeakGrushin.weakGrushinGradientEnergy_eq_cutoff_one
#check @TheoremT.Continuum.WeakGrushin.compact_smooth_jet_energy
#check @TheoremT.Continuum.WeakGrushin.compact_weakH2_energy
#check @TheoremT.Continuum.WeakGrushin.weakGrushinGradientEnergy_nonneg
#check @TheoremT.Continuum.WeakGrushin.weakGrushin_y_gradient_le_energy
#check @TheoremT.Continuum.WeakGrushin.compact_weakH2_energy_cauchy
#check @TheoremT.Continuum.WeakGrushin.compact_weakH2_energy_output
#check @TheoremT.Continuum.WeakGrushin.compact_weakH2_y_gradient_square_output

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.weakGrushinGradientEnergy
#print axioms TheoremT.Continuum.WeakGrushin.weakGrushinGradientEnergy_eq_cutoff_one
#print axioms TheoremT.Continuum.WeakGrushin.compact_smooth_jet_energy
#print axioms TheoremT.Continuum.WeakGrushin.compact_weakH2_energy
#print axioms TheoremT.Continuum.WeakGrushin.weakGrushinGradientEnergy_nonneg
#print axioms TheoremT.Continuum.WeakGrushin.weakGrushin_y_gradient_le_energy
#print axioms TheoremT.Continuum.WeakGrushin.compact_weakH2_energy_cauchy
#print axioms TheoremT.Continuum.WeakGrushin.compact_weakH2_energy_output
#print axioms TheoremT.Continuum.WeakGrushin.compact_weakH2_y_gradient_square_output
