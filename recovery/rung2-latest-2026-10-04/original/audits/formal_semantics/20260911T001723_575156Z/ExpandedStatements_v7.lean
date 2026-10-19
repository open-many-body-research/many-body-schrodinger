import ProductWeakWordMollification_v1

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
#check @TheoremT.Continuum.productMollifiedWord
#check @TheoremT.Continuum.productMollifiedWordLp
#check @TheoremT.Continuum.productMollifiedWord_contDiff
#check @TheoremT.Continuum.productMollifiedWord_directional
#check @TheoremT.Continuum.productMollifiedWordLp_ae
#check @TheoremT.Continuum.productMollifiedWordLp_tendsto
#check @TheoremT.Continuum.productMollifiedWordLp_norm_le

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.productMollifiedWord
#print axioms TheoremT.Continuum.productMollifiedWordLp
#print axioms TheoremT.Continuum.productMollifiedWord_contDiff
#print axioms TheoremT.Continuum.productMollifiedWord_directional
#print axioms TheoremT.Continuum.productMollifiedWordLp_ae
#print axioms TheoremT.Continuum.productMollifiedWordLp_tendsto
#print axioms TheoremT.Continuum.productMollifiedWordLp_norm_le
