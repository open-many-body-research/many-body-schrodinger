import ManyBody.S8.Internal.NuclearChartBounds

/-!
Positive-radius versions of the same actual two-electron nuclear chart.
The squared KS radius condition is the literal physical selected radius.
Only the zeroth-order potential bound becomes uniform for 0 < r <= 1;
no radius-independent cutoff or derivative constant is asserted.
-/
noncomputable section
open scoped BigOperators
open TheoremT.Continuum

namespace ManyBody.S8

/-- The actual spectator position has center norm r; the selected physical
radius is bounded through the exact squared KS norm. -/
def nuclearChartScaledOpen (r : ℝ) (t0 : Position) : Set (NuclearKSSpace (0 : Fin 2)) :=
  {q | ‖q.1‖ ^ 2 < r / 16 ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ < r / 4}

theorem nuclearChartScaledOpen_isOpen (r : ℝ) (t0 : Position) :
    IsOpen (nuclearChartScaledOpen r t0) := by
  have ht : Continuous (fun q : NuclearKSSpace (0 : Fin 2) =>
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)) :=
    (continuous_position (1 : Fin 2)).comp (nuclearKSLift_contDiff (0 : Fin 2)).continuous
  exact (isOpen_lt (continuous_fst.norm.pow 2) continuous_const).inter
    (isOpen_lt (ht.sub continuous_const).norm continuous_const)

theorem nuclearChartScaled_closed_geometry
    (r : ℝ) (_hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = r)
    {q : NuclearKSSpace (0 : Fin 2)} (hY : ‖q.1‖ ^ 2 ≤ r / 16)
    (hT : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ r / 4) :
    3 * r / 4 ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ≤ 5 * r / 4 ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2)‖ ≤ r / 16 ∧
    11 * r / 16 ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by
  have hlo := norm_sub_norm_le t0 (position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2))
  rw [ht0, norm_sub_rev] at hlo
  have hup := norm_sub_norm_le (position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)) t0
  rw [ht0] at hup
  have htl : 3 * r / 4 ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by
    linarith
  have htu : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ≤ 5 * r / 4 := by
    linarith
  have hx : ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2)‖ ≤ r / 16 := by
    rw [nuclearKSLift_nuclear_radius]
    exact hY
  have hpair := norm_sub_norm_le
    (position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2))
    (position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2))
  rw [norm_sub_rev] at hpair
  exact ⟨htl, htu, hx, by linarith⟩

theorem nuclearChartScaled_closed_geometry_of_sqrt
    (r : ℝ) (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = r)
    {q : NuclearKSSpace (0 : Fin 2)} (hY : ‖q.1‖ ≤ Real.sqrt r / 4)
    (hT : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ r / 4) :
    3 * r / 4 ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ≤ 5 * r / 4 ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2)‖ ≤ r / 16 ∧
    11 * r / 16 ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by
  have hsq := (sq_le_sq₀ (norm_nonneg q.1) (by positivity : 0 ≤ Real.sqrt r / 4)).mpr hY
  have hsqrt := Real.sq_sqrt hr.le
  apply nuclearChartScaled_closed_geometry r hr t0 ht0 (hT := hT)
  nlinarith

theorem nuclearChartScaled_closed_subset_coefficientPatch
    (r : ℝ) (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = r)
    {q : NuclearKSSpace (0 : Fin 2)} (hY : ‖q.1‖ ^ 2 ≤ r / 16)
    (hT : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ r / 4) :
    q ∈ nuclearKSCoefficientPatch (0 : Fin 2) := by
  obtain ⟨htl, _, _, hpair⟩ := nuclearChartScaled_closed_geometry r hr t0 ht0 hY hT
  have htp : 0 < ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by
    linarith
  have hpp : 0 < ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by linarith
  have hother := norm_pos_iff.mp htp
  have hne := sub_ne_zero.mp (norm_pos_iff.mp hpp)
  constructor
  · intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact hother
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact False.elim (hjk rfl)
    · exact hne
    · exact Ne.symm hne
    · exact False.elim (hjk rfl)

theorem nuclearChartScaledOpen_subset_coefficientPatch
    (r : ℝ) (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = r) :
    nuclearChartScaledOpen r t0 ⊆ nuclearKSCoefficientPatch (0 : Fin 2) := by
  intro q hq
  exact nuclearChartScaled_closed_subset_coefficientPatch r hr t0 ht0 hq.1.le hq.2.le

theorem nuclearKSPotential_norm_le_of_scaled_closed_chart
    (Z E r : ℝ) (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = r)
    {q : NuclearKSSpace (0 : Fin 2)} (hY : ‖q.1‖ ^ 2 ≤ r / 16)
    (hT : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ r / 4) :
    ‖nuclearKSPotential (0 : Fin 2) Z E q‖ ≤
      (26 / 3 : ℝ) * |Z| + 8 / 11 + r * |E| / 2 := by
  obtain ⟨htl, _, _, hpair⟩ := nuclearChartScaled_closed_geometry r hr t0 ht0 hY hT
  have htp : 0 < ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by linarith
  have hpp : 0 < ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by linarith
  have hti : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹ ≤ (4 / 3 : ℝ) / r := by
    calc
      _ ≤ (3 * r / 4)⁻¹ := (inv_le_inv₀ htp (by positivity)).mpr htl
      _ = _ := by field_simp [hr.ne']
  have hpi : ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹ ≤ (16 / 11 : ℝ) / r := by
    calc
      _ ≤ (11 * r / 16)⁻¹ := (inv_le_inv₀ hpp (by positivity)).mpr hpair
      _ = _ := by field_simp [hr.ne']
  have hV : ‖coulombWithoutSelectedNucleus (0 : Fin 2) Z (nuclearKSLift (0 : Fin 2) q)‖ ≤
      |Z| * ((4 / 3 : ℝ) / r) + (16 / 11 : ℝ) / r := by
    rw [coulombWithoutSelectedNucleus_two_electrons]
    calc
      _ ≤ ‖-Z * ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹‖ +
          ‖‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
            position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹‖ := norm_add_le _ _
      _ = |Z| * ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹ +
          ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
            position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹ := by
        simp [norm_mul, norm_neg, Real.norm_eq_abs]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hti (abs_nonneg Z)) hpi
  have hVE : ‖coulombWithoutSelectedNucleus (0 : Fin 2) Z (nuclearKSLift (0 : Fin 2) q) - E‖ ≤
      |Z| * ((4 / 3 : ℝ) / r) + (16 / 11 : ℝ) / r + |E| :=
    (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs] using add_le_add hV (le_refl ‖E‖))
  rw [nuclearKSPotential]
  calc
    _ ≤ ‖-8 * Z‖ + ‖8 * ‖q.1‖ ^ 2 *
        (coulombWithoutSelectedNucleus (0 : Fin 2) Z (nuclearKSLift (0 : Fin 2) q) - E)‖ := norm_add_le _ _
    _ = 8 * |Z| + 8 * ‖q.1‖ ^ 2 *
        ‖coulombWithoutSelectedNucleus (0 : Fin 2) Z (nuclearKSLift (0 : Fin 2) q) - E‖ := by
      simp [norm_mul, Real.norm_eq_abs]
    _ ≤ 8 * |Z| + 8 * ‖q.1‖ ^ 2 *
        (|Z| * ((4 / 3 : ℝ) / r) + (16 / 11 : ℝ) / r + |E|) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hVE (by positivity))
    _ ≤ 8 * |Z| + (r / 2) * (|Z| * ((4 / 3 : ℝ) / r) + (16 / 11 : ℝ) / r + |E|) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (by nlinarith) (by positivity))
    _ = _ := by
      field_simp [hr.ne']
      ring

theorem nuclearKSPotential_norm_le_of_mem_nuclearChartScaledOpen
    (Z E r : ℝ) (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = r)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ nuclearChartScaledOpen r t0) :
    ‖nuclearKSPotential (0 : Fin 2) Z E q‖ ≤
      (26 / 3 : ℝ) * |Z| + 8 / 11 + r * |E| / 2 :=
  nuclearKSPotential_norm_le_of_scaled_closed_chart Z E r hr t0 ht0 hq.1.le hq.2.le

theorem nuclearKSPotential_uniform_norm_le_of_mem_nuclearChartScaledOpen
    (Z E r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (t0 : Position) (ht0 : ‖t0‖ = r)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ nuclearChartScaledOpen r t0) :
    ‖nuclearKSPotential (0 : Fin 2) Z E q‖ ≤
      (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2 := by
  have h := nuclearKSPotential_norm_le_of_mem_nuclearChartScaledOpen Z E r hr t0 ht0 hq
  have he := mul_le_mul_of_nonneg_right hr1 (abs_nonneg E)
  linarith

#print axioms nuclearChartScaledOpen_isOpen
#print axioms nuclearChartScaled_closed_geometry_of_sqrt
#print axioms nuclearChartScaledOpen_subset_coefficientPatch
#print axioms nuclearKSPotential_norm_le_of_mem_nuclearChartScaledOpen
#print axioms nuclearKSPotential_uniform_norm_le_of_mem_nuclearChartScaledOpen

end ManyBody.S8
