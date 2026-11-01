import KSCommonAnnulusFactorialJets_v1
import KSCommonAnnulusFactorialWords_v1

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
#check @TheoremT.Continuum.KSScaledFactorialJetControl
#check @TheoremT.Continuum.ksScaledFactorialJetControl_mono
#check @TheoremT.Continuum.ksScaledFactorialJetControl_subset
#check @TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_jets
#check @TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_physical_boxes
#check @TheoremT.Continuum.KSScaledFactorialWordControl
#check @TheoremT.Continuum.ksScaledFactorialWordControl_of_jets
#check @TheoremT.Continuum.ksScaledFactorialWordControl_subset
#check @TheoremT.Continuum.ksScaledFactorialWordControl_physical_word
#check @TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_jet_word_control
#check @TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_physical_box_data

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.KSScaledFactorialJetControl
#print axioms TheoremT.Continuum.ksScaledFactorialJetControl_mono
#print axioms TheoremT.Continuum.ksScaledFactorialJetControl_subset
#print axioms TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_jets
#print axioms TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_physical_boxes
#print axioms TheoremT.Continuum.KSScaledFactorialWordControl
#print axioms TheoremT.Continuum.ksScaledFactorialWordControl_of_jets
#print axioms TheoremT.Continuum.ksScaledFactorialWordControl_subset
#print axioms TheoremT.Continuum.ksScaledFactorialWordControl_physical_word
#print axioms TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_jet_word_control
#print axioms TheoremT.Continuum.ksCommonAnnulus_uniform_factorial_physical_box_data
