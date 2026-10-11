import CoordinateWordLinearEquivTransport_v1
import SevenCoordinateRepresentativeReturn_v1
import ProductLocalWeakWordsPhysicalRepresentative_v1

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
#check @TheoremT.Continuum.normed_word_linearEquiv_transport
#check @TheoremT.Continuum.normed_word_eq_product_word
#check @TheoremT.Continuum.sevenToProduct_all_word_chain
#check @TheoremT.Continuum.sevenToProduct_symm_direction
#check @TheoremT.Continuum.sevenToProduct_symm_all_word_chain
#check @TheoremT.Continuum.sevenToProduct_symm_measurePreserving
#check @TheoremT.Continuum.sevenToProduct_ae_return
#check @TheoremT.Continuum.seven_coordinate_smooth_representative_return
#check @TheoremT.Continuum.product_local_weak_words_physical_quantitative_representative

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.normed_word_linearEquiv_transport
#print axioms TheoremT.Continuum.normed_word_eq_product_word
#print axioms TheoremT.Continuum.sevenToProduct_all_word_chain
#print axioms TheoremT.Continuum.sevenToProduct_symm_direction
#print axioms TheoremT.Continuum.sevenToProduct_symm_all_word_chain
#print axioms TheoremT.Continuum.sevenToProduct_symm_measurePreserving
#print axioms TheoremT.Continuum.sevenToProduct_ae_return
#print axioms TheoremT.Continuum.seven_coordinate_smooth_representative_return
#print axioms TheoremT.Continuum.product_local_weak_words_physical_quantitative_representative
