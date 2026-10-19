import PhysicalH12ConcreteStepGeometry_v1
import PhysicalH12IterationSchedule_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteInnerCutoff
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteEnergyCutoff
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_isOpen
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_measurableSet
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_antitone
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_zero
#check @TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_34
#check @TheoremT.Continuum.WeakGrushin.physical_h12_concrete_step_geometry
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleMiddle
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleInnerCutoff
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleEnergyCutoff
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_isOpen
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_measurableSet
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_antitone
#check @TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_subset_initial
#check @TheoremT.Continuum.WeakGrushin.physical_h12_schedule_geometry
#check @TheoremT.Continuum.WeakGrushin.physical_h12_T12_geometry
#check @TheoremT.Continuum.WeakGrushin.physical_h12_Y5_geometry
#check @TheoremT.Continuum.WeakGrushin.physicalH12Schedule_T12_Y5_join
#check @TheoremT.Continuum.WeakGrushin.physicalH12Schedule_initial
#check @TheoremT.Continuum.WeakGrushin.physicalH12Schedule_terminal

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteInnerCutoff
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteEnergyCutoff
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_isOpen
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_measurableSet
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_antitone
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_zero
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ConcreteBox_34
#print axioms TheoremT.Continuum.WeakGrushin.physical_h12_concrete_step_geometry
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleMiddle
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleInnerCutoff
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleEnergyCutoff
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_isOpen
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_measurableSet
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_antitone
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12ScheduleRegion_subset_initial
#print axioms TheoremT.Continuum.WeakGrushin.physical_h12_schedule_geometry
#print axioms TheoremT.Continuum.WeakGrushin.physical_h12_T12_geometry
#print axioms TheoremT.Continuum.WeakGrushin.physical_h12_Y5_geometry
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12Schedule_T12_Y5_join
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12Schedule_initial
#print axioms TheoremT.Continuum.WeakGrushin.physicalH12Schedule_terminal
