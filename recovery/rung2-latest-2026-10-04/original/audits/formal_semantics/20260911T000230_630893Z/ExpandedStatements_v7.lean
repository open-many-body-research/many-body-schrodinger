import ProductBoxAverageMeasure_v1

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
#check @TheoremT.Continuum.productBoxVolume
#check @TheoremT.Continuum.productBoxVolume_pos
#check @TheoremT.Continuum.volume_product_closed_box
#check @TheoremT.Continuum.volume_product_closed_box_of_lt
#check @TheoremT.Continuum.product_interval_average_measure_eq
#check @TheoremT.Continuum.product_box_average_integral_norm_le_L2
#check @TheoremT.Continuum.product_box_average_lintegral_enorm_le_L2
#check @TheoremT.Continuum.product_box_average_lintegral_indicator_enorm_le_L2

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.productBoxVolume
#print axioms TheoremT.Continuum.productBoxVolume_pos
#print axioms TheoremT.Continuum.volume_product_closed_box
#print axioms TheoremT.Continuum.volume_product_closed_box_of_lt
#print axioms TheoremT.Continuum.product_interval_average_measure_eq
#print axioms TheoremT.Continuum.product_box_average_integral_norm_le_L2
#print axioms TheoremT.Continuum.product_box_average_lintegral_enorm_le_L2
#print axioms TheoremT.Continuum.product_box_average_lintegral_indicator_enorm_le_L2
