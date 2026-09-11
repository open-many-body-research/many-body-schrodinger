import ConfigurationSlicing_v2
import HardyLimitComplex_v1

/-! Sliced compact-C1 nuclear Hardy on the actual R^(3N) configuration space.
No weak Sobolev slicing premise, spin factor, or nonphysical norm is introduced. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff
set_option maxHeartbeats 800000

namespace TheoremT.Continuum

def electronInsertion {N : ℕ} (i : Fin N) : Position →L[ℝ] Configuration N :=
  (configurationProductEquiv i).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ Position (SpectatorConfiguration i))

theorem electronInsertion_eq_reassemble_zero {N : ℕ} (i : Fin N) (y : Position) :
    electronInsertion i y = configurationReassemble i y 0 := rfl

theorem electronInsertion_apply {N : ℕ} (i : Fin N) (y : Position) (q : Coordinate N) :
    electronInsertion i y q = if q.1 = i then y q.2 else 0 := by
  rw [electronInsertion_eq_reassemble_zero]
  by_cases h : q.1 = i
  · rcases q with ⟨j, k⟩
    change j = i at h
    subst j
    simp only [ite_true]
    exact congrArg (fun p : Position => p k) (configurationReassemble_position i y 0)
  · simp only [h, ite_false]
    exact configurationReassemble_spectator i y 0 ⟨q, h⟩

theorem electronInsertion_basis {N : ℕ} (i : Fin N) (k : Fin 3) :
    electronInsertion i (TheoremT.Hardy.basisVector k) = coordinateVector (i, k) := by
  apply (WithLp.ext_iff 2).mpr
  funext q
  rcases q with ⟨j, l⟩
  rw [electronInsertion_apply]
  by_cases h : j = i
  · subst j
    simp [TheoremT.Hardy.basisVector, coordinateVector]
  · simp [h, coordinateVector]

theorem configurationReassemble_hasFDerivAt {N : ℕ} (i : Fin N)
    (s : SpectatorConfiguration i) (y : Position) :
    HasFDerivAt (fun z => configurationReassemble i z s) (electronInsertion i) y :=
  (configurationProductEquiv i).symm.hasFDerivAt.comp y (hasFDerivAt_prodMk_left y s)

theorem contDiff_configurationReassemble_left {N : ℕ} (i : Fin N)
    (s : SpectatorConfiguration i) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y => configurationReassemble i y s) :=
  (configurationProductEquiv i).symm.contDiff.comp (contDiff_id.prodMk contDiff_const)

theorem compactSupport_configuration_slice {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (huc : HasCompactSupport u)
    (s : SpectatorConfiguration i) :
    HasCompactSupport (fun y => u (configurationReassemble i y s)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (huc.isCompact.image (continuous_position i))
  intro y hy
  refine ⟨configurationReassemble i y s, ?_, configurationReassemble_position i y s⟩
  exact subset_tsupport u hy

theorem configuration_slice_fderiv_basis {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u)
    (s : SpectatorConfiguration i) (y : Position) (k : Fin 3) :
    fderiv ℝ (fun z => u (configurationReassemble i z s)) y (TheoremT.Hardy.basisVector k) =
      fderiv ℝ u (configurationReassemble i y s) (coordinateVector (i, k)) := by
  have hd := ((hu.differentiable (by norm_num) (configurationReassemble i y s)).hasFDerivAt).comp
    y (configurationReassemble_hasFDerivAt i s y)
  have hv := congrArg (fun L : Position →L[ℝ] ℂ => L (TheoremT.Hardy.basisVector k)) hd.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, electronInsertion_basis] using hv

def electronGradientEnergy {N : ℕ} (i : Fin N) (u : Configuration N → ℂ)
    (x : Configuration N) : ℝ :=
  ∑ k : Fin 3, ‖fderiv ℝ u x (coordinateVector (i, k))‖ ^ 2

theorem electronGradientEnergy_integrable {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (electronGradientEnergy i u) volume := by
  apply integrable_finsetSum
  intro k _
  have hd : Continuous (fun x => fderiv ℝ u x (coordinateVector (i, k))) :=
    (hu.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  apply (hd.norm.pow 2).integrable_of_hasCompactSupport
  apply (huc.fderiv_apply ℝ (coordinateVector (i, k))).mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  apply hx
  change ‖fderiv ℝ u x (coordinateVector (i, k))‖ ^ 2 = 0
  rw [hz]
  simp

/-- The compact three-dimensional Hardy theorem on every physical electron slice. -/
theorem nuclear_hardy_on_slice {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (s : SpectatorConfiguration i) :
    Integrable (fun y : Position => ‖u (configurationReassemble i y s)‖^2 / ‖y‖^2) volume ∧
      (∫ y : Position, ‖u (configurationReassemble i y s)‖^2 / ‖y‖^2) ≤
        4 * (∫ y : Position, electronGradientEnergy i u (configurationReassemble i y s)) := by
  have h := TheoremT.Hardy.complex_hardy_integrable_sq_and_bound
    (hu.comp (contDiff_configurationReassemble_left i s)) (compactSupport_configuration_slice i huc s)
  simpa only [Function.comp_def, configuration_slice_fderiv_basis i hu, electronGradientEnergy] using h

/-- A nonnegative slice bound, together with an integrable majorant, proves
global integrability before applying Fubini. The explicit slice premises are
discharged by `nuclear_hardy_on_slice` in the application below. -/
theorem integrable_and_bound_of_slices {N : ℕ} (i : Fin N)
    (F G : Configuration N → ℝ) (c : ℝ) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hG : Integrable G volume)
    (hFi : ∀ s : SpectatorConfiguration i,
      Integrable (fun y : Position => F (configurationReassemble i y s)) volume)
    (hFG : ∀ s : SpectatorConfiguration i,
      (∫ y : Position, F (configurationReassemble i y s)) ≤
        c * (∫ y : Position, G (configurationReassemble i y s))) :
    Integrable F volume ∧ (∫ x, F x) ≤ c * (∫ x, G x) := by
  let R : Position × SpectatorConfiguration i → Configuration N :=
    fun ys => configurationReassemble i ys.1 ys.2
  have hR : MeasurePreserving R
      ((volume : Measure Position).prod (volume : Measure (SpectatorConfiguration i))) volume :=
    configurationReassemble_measurePreserving i
  have hRe : MeasurableEmbedding R := (configurationProductEquiv i).symm.toHomeomorph.measurableEmbedding
  have hFp : AEStronglyMeasurable (F ∘ R)
      ((volume : Measure Position).prod (volume : Measure (SpectatorConfiguration i))) :=
    (hF.comp hR.measurable).aestronglyMeasurable
  have hGp : Integrable (G ∘ R)
      ((volume : Measure Position).prod (volume : Measure (SpectatorConfiguration i))) :=
    hR.integrable_comp_of_integrable hG
  have hnorm (s : SpectatorConfiguration i) :
      (∫ y : Position, ‖F (R (y, s))‖) = (∫ y : Position, F (R (y, s))) := by
    apply integral_congr_ae
    exact .of_forall (fun y => Real.norm_of_nonneg (hF0 (R (y, s))))
  have houter : Integrable (fun s : SpectatorConfiguration i =>
      ∫ y : Position, ‖F (R (y, s))‖) volume := by
    apply (hGp.integral_prod_right.const_mul c).mono_nonneg
      hFp.norm.prod_swap.integral_prod_right'
    · exact .of_forall (fun s => integral_nonneg (fun y => norm_nonneg _))
    · exact .of_forall (fun s => by
        change (∫ y : Position, ‖F (R (y, s))‖) ≤ c * (∫ y : Position, G (R (y, s)))
        rw [hnorm]
        exact hFG s)
  have hFpI : Integrable (F ∘ R)
      ((volume : Measure Position).prod (volume : Measure (SpectatorConfiguration i))) :=
    (integrable_prod_iff' hFp).mpr ⟨.of_forall hFi, houter⟩
  have hFI : Integrable F volume := (hR.integrable_comp hF.aestronglyMeasurable).mp hFpI
  refine ⟨hFI, ?_⟩
  rw [← hR.integral_comp hRe F,
    integral_prod_symm (fun ys : Position × SpectatorConfiguration i => F (R ys)) hFpI]
  calc
    _ ≤ ∫ s : SpectatorConfiguration i, c * (∫ y : Position, G (R (y, s))) :=
      integral_mono hFpI.integral_prod_right (hGp.integral_prod_right.const_mul c) hFG
    _ = c * (∫ ys : Position × SpectatorConfiguration i, G (R ys)
        ∂(volume : Measure Position).prod (volume : Measure (SpectatorConfiguration i))) := by
      rw [integral_const_mul,
        ← integral_prod_symm (fun ys : Position × SpectatorConfiguration i => G (R ys)) hGp]
    _ = c * (∫ x : Configuration N, G x) := by rw [hR.integral_comp hRe G]

/-- Nuclear Hardy, constant four, for every complex compact C1 function on the
actual R^(3N), using only the three derivatives of electron i. -/
theorem compact_nuclear_hardy_integrable_sq_and_bound {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x : Configuration N => ‖u x‖^2 / ‖position x i‖^2) volume ∧
      (∫ x : Configuration N, ‖u x‖^2 / ‖position x i‖^2) ≤
        4 * (∫ x : Configuration N, electronGradientEnergy i u x) := by
  apply integrable_and_bound_of_slices i _ (electronGradientEnergy i u) 4
  · exact (hu.continuous.measurable.norm.pow_const 2).div
      ((continuous_position i).measurable.norm.pow_const 2)
  · intro x
    positivity
  · exact electronGradientEnergy_integrable i hu huc
  · intro s
    simpa only [configurationReassemble_position] using (nuclear_hardy_on_slice i hu huc s).1
  · intro s
    simpa only [configurationReassemble_position] using (nuclear_hardy_on_slice i hu huc s).2

#print axioms electronInsertion_apply
#print axioms electronInsertion_basis
#print axioms configurationReassemble_hasFDerivAt
#print axioms contDiff_configurationReassemble_left
#print axioms compactSupport_configuration_slice
#print axioms configuration_slice_fderiv_basis
#print axioms electronGradientEnergy_integrable
#print axioms nuclear_hardy_on_slice
#print axioms integrable_and_bound_of_slices
#print axioms compact_nuclear_hardy_integrable_sq_and_bound

end TheoremT.Continuum
