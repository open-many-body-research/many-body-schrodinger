import ProductCoordinateWeakHk_v1
import ProductCoordinateWeakWordTests_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.coordinateYWord
#check @TheoremT.Continuum.WeakGrushin.coordinateTWord
#check @TheoremT.Continuum.WeakGrushin.productCoordinateDirection
#check @TheoremT.Continuum.WeakGrushin.coordinateWord_length
#check @TheoremT.Continuum.WeakGrushin.ProductCoordinateWeakHk
#check @TheoremT.Continuum.WeakGrushin.mixedTriangularState_coordinateWeakHk
#check @TheoremT.Continuum.WeakGrushin.productCoordinateTestWord
#check @TheoremT.Continuum.WeakGrushin.productCoordinateTestWord_contDiff
#check @TheoremT.Continuum.WeakGrushin.productCoordinateTestWord_compact
#check @TheoremT.Continuum.WeakGrushin.productCoordinateTestWord_support
#check @TheoremT.Continuum.WeakGrushin.product_coordinate_family_test_identity
#check @TheoremT.Continuum.WeakGrushin.product_coordinate_family_tests_integrable

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.coordinateYWord
#print axioms TheoremT.Continuum.WeakGrushin.coordinateTWord
#print axioms TheoremT.Continuum.WeakGrushin.productCoordinateDirection
#print axioms TheoremT.Continuum.WeakGrushin.coordinateWord_length
#print axioms TheoremT.Continuum.WeakGrushin.ProductCoordinateWeakHk
#print axioms TheoremT.Continuum.WeakGrushin.mixedTriangularState_coordinateWeakHk
#print axioms TheoremT.Continuum.WeakGrushin.productCoordinateTestWord
#print axioms TheoremT.Continuum.WeakGrushin.productCoordinateTestWord_contDiff
#print axioms TheoremT.Continuum.WeakGrushin.productCoordinateTestWord_compact
#print axioms TheoremT.Continuum.WeakGrushin.productCoordinateTestWord_support
#print axioms TheoremT.Continuum.WeakGrushin.product_coordinate_family_test_identity
#print axioms TheoremT.Continuum.WeakGrushin.product_coordinate_family_tests_integrable
