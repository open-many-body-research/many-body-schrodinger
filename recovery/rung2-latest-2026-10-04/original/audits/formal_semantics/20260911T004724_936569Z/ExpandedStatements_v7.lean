import ProductSevenCoordinateTransport_v1
import ProductSevenMollifierLimits_v1
import ProductCompactAllWeakWords_v1

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
#check @TheoremT.Continuum.sevenToProduct
#check @TheoremT.Continuum.sevenToProduct_measurePreserving
#check @TheoremT.Continuum.sevenToProduct_direction
#check @TheoremT.Continuum.sevenToProduct_word_chain
#check @TheoremT.Continuum.sevenProductL2Pullback
#check @TheoremT.Continuum.sevenRestrictL2
#check @TheoremT.Continuum.productSevenMollifier
#check @TheoremT.Continuum.productSevenWordLimit
#check @TheoremT.Continuum.productSevenMollifiedWordLp
#check @TheoremT.Continuum.productSevenMollifier_contDiff
#check @TheoremT.Continuum.productSevenWordLimit_ae
#check @TheoremT.Continuum.productSevenMollifiedWordLp_ae
#check @TheoremT.Continuum.productSevenMollifiedWordLp_tendsto
#check @TheoremT.Continuum.product_weak_words7_continuous_representatives
#check @TheoremT.Continuum.product_compact_local_all_weak_words_global
#check @TheoremT.Continuum.product_compact_cutoff_all_weak_word_family

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.sevenToProduct
#print axioms TheoremT.Continuum.sevenToProduct_measurePreserving
#print axioms TheoremT.Continuum.sevenToProduct_direction
#print axioms TheoremT.Continuum.sevenToProduct_word_chain
#print axioms TheoremT.Continuum.sevenProductL2Pullback
#print axioms TheoremT.Continuum.sevenRestrictL2
#print axioms TheoremT.Continuum.productSevenMollifier
#print axioms TheoremT.Continuum.productSevenWordLimit
#print axioms TheoremT.Continuum.productSevenMollifiedWordLp
#print axioms TheoremT.Continuum.productSevenMollifier_contDiff
#print axioms TheoremT.Continuum.productSevenWordLimit_ae
#print axioms TheoremT.Continuum.productSevenMollifiedWordLp_ae
#print axioms TheoremT.Continuum.productSevenMollifiedWordLp_tendsto
#print axioms TheoremT.Continuum.product_weak_words7_continuous_representatives
#print axioms TheoremT.Continuum.product_compact_local_all_weak_words_global
#print axioms TheoremT.Continuum.product_compact_cutoff_all_weak_word_family
