import ProductCoordinateWordSpectatorTrace_v1
import WeakGrushinCoordinateWordEquation_v1

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
#check @TheoremT.Continuum.WeakGrushin.coordinateWordSpectatorTrace
#check @TheoremT.Continuum.WeakGrushin.coordinateWordSpectatorTrace_locallyL2
#check @TheoremT.Continuum.WeakGrushin.coordinateWordSpectatorTrace_localD
#check @TheoremT.Continuum.WeakGrushin.coordinate_word_appended_second_spectator
#check @TheoremT.Continuum.WeakGrushin.coordinateWordYSource
#check @TheoremT.Continuum.WeakGrushin.coordinateWordGrushinSource
#check @TheoremT.Continuum.WeakGrushin.coordinateWordGrushinSource_eq
#check @TheoremT.Continuum.WeakGrushin.weak_grushin_coordinate_word_equations

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.coordinateWordSpectatorTrace
#print axioms TheoremT.Continuum.WeakGrushin.coordinateWordSpectatorTrace_locallyL2
#print axioms TheoremT.Continuum.WeakGrushin.coordinateWordSpectatorTrace_localD
#print axioms TheoremT.Continuum.WeakGrushin.coordinate_word_appended_second_spectator
#print axioms TheoremT.Continuum.WeakGrushin.coordinateWordYSource
#print axioms TheoremT.Continuum.WeakGrushin.coordinateWordGrushinSource
#print axioms TheoremT.Continuum.WeakGrushin.coordinateWordGrushinSource_eq
#print axioms TheoremT.Continuum.WeakGrushin.weak_grushin_coordinate_word_equations
