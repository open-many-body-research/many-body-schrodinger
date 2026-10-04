import IntervalPointwiseFTC_v1
import IntervalPointwiseL2_v1
import IntervalPointwiseAverage_v1

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
#check @TheoremT.Continuum.interval_norm_sub_le_derivative_integral
#check @TheoremT.Continuum.interval_pointwise_norm_mul_length_le
#check @TheoremT.Continuum.interval_pointwise_norm_le_average_derivative
#check @TheoremT.Continuum.finite_measure_integral_norm_le_sqrt
#check @TheoremT.Continuum.interval_integral_norm_le_sqrt
#check @TheoremT.Continuum.interval_pointwise_norm_le_L2
#check @TheoremT.Continuum.intervalAverageMeasure
#check @TheoremT.Continuum.intervalAverageMeasure_univ
#check @TheoremT.Continuum.interval_pointwise_enorm_le_average_derivative

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.interval_norm_sub_le_derivative_integral
#print axioms TheoremT.Continuum.interval_pointwise_norm_mul_length_le
#print axioms TheoremT.Continuum.interval_pointwise_norm_le_average_derivative
#print axioms TheoremT.Continuum.finite_measure_integral_norm_le_sqrt
#print axioms TheoremT.Continuum.interval_integral_norm_le_sqrt
#print axioms TheoremT.Continuum.interval_pointwise_norm_le_L2
#print axioms TheoremT.Continuum.intervalAverageMeasure
#print axioms TheoremT.Continuum.intervalAverageMeasure_univ
#print axioms TheoremT.Continuum.interval_pointwise_enorm_le_average_derivative
