import NuclearKSPotential_v1
import CoulombTwoElectronExpectation_v1

/-!
A fixed actual two-electron nuclear KS chart centered at a unit spectator
position. The chart is described using the existing physical lift and other
electron position, without identifying spectator coordinate spaces.

The selected nuclear collision is included. The other nuclear and pair
collisions are excluded by quantitative distance bounds. No physical
potential, operator, or ambient space is redefined.
-/
noncomputable section
open scoped BigOperators
open TheoremT.Continuum

namespace ManyBody.S8

/-- An open chart in the existing nuclear KS space, with the other electron
position within 1/4 of a fixed physical center. -/
def nuclearChartOpen (t0 : Position) : Set (NuclearKSSpace (0 : Fin 2)) :=
  {q | ‖q.1‖ < (1 / 4 : ℝ) ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ < (1 / 4 : ℝ)}

theorem nuclearChartOpen_isOpen (t0 : Position) : IsOpen (nuclearChartOpen t0) := by
  have ht : Continuous (fun q : NuclearKSSpace (0 : Fin 2) =>
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)) := by
    exact (continuous_position (1 : Fin 2)).comp
      (nuclearKSLift_contDiff (0 : Fin 2)).continuous
  exact (isOpen_lt continuous_fst.norm continuous_const).inter
    (isOpen_lt (ht.sub continuous_const).norm continuous_const)

theorem nuclearChart_closed_geometry
    (t0 : Position) (ht0 : ‖t0‖ = 1) {q : NuclearKSSpace (0 : Fin 2)}
    (hY : ‖q.1‖ ≤ (1 / 4 : ℝ))
    (hT : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ (1 / 4 : ℝ)) :
    (3 / 4 : ℝ) ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ≤ (5 / 4 : ℝ) ∧
    ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2)‖ ≤ (1 / 16 : ℝ) ∧
    (11 / 16 : ℝ) ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by
  have hlo := norm_sub_norm_le t0 (position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2))
  rw [ht0, norm_sub_rev] at hlo
  have hup := norm_sub_norm_le (position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)) t0
  rw [ht0] at hup
  have htl : (3 / 4 : ℝ) ≤ ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by
    linarith
  have htu : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ ≤ (5 / 4 : ℝ) := by
    linarith
  have hsq : ‖q.1‖ ^ 2 ≤ (1 / 16 : ℝ) := by
    have h := (sq_le_sq₀ (norm_nonneg q.1) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hY
    norm_num at h
    exact h
  have hx : ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2)‖ ≤ (1 / 16 : ℝ) := by
    rw [nuclearKSLift_nuclear_radius]
    exact hsq
  have hpair := norm_sub_norm_le
    (position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2))
    (position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2))
  rw [norm_sub_rev] at hpair
  exact ⟨htl, htu, hx, by linarith⟩

theorem nuclearChart_closed_subset_coefficientPatch
    (t0 : Position) (ht0 : ‖t0‖ = 1) {q : NuclearKSSpace (0 : Fin 2)}
    (hY : ‖q.1‖ ≤ (1 / 4 : ℝ))
    (hT : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ (1 / 4 : ℝ)) :
    q ∈ nuclearKSCoefficientPatch (0 : Fin 2) := by
  obtain ⟨htl, _, _, hpair⟩ := nuclearChart_closed_geometry t0 ht0 hY hT
  have hother : position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) htl)
  have hne : position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) ≠
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) :=
    sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11 / 16) hpair))
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

theorem nuclearChartOpen_subset_coefficientPatch
    (t0 : Position) (ht0 : ‖t0‖ = 1) :
    nuclearChartOpen t0 ⊆ nuclearKSCoefficientPatch (0 : Fin 2) := by
  intro q hq
  exact nuclearChart_closed_subset_coefficientPatch t0 ht0 hq.1.le hq.2.le

theorem coulombWithoutSelectedNucleus_two_electrons (Z : ℝ) (x : Configuration 2) :
    coulombWithoutSelectedNucleus (0 : Fin 2) Z x =
      -Z * ‖position x (1 : Fin 2)‖⁻¹ +
        ‖position x (0 : Fin 2) - position x (1 : Fin 2)‖⁻¹ := by
  have h := coulomb_split_selected_nucleus (0 : Fin 2) Z x
  rw [coulombPotential_two_electrons] at h
  linarith

theorem nuclearKSPotential_norm_le_of_closed_chart
    (Z E : ℝ) (t0 : Position) (ht0 : ‖t0‖ = 1) {q : NuclearKSSpace (0 : Fin 2)}
    (hY : ‖q.1‖ ≤ (1 / 4 : ℝ))
    (hT : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ (1 / 4 : ℝ)) :
    ‖nuclearKSPotential (0 : Fin 2) Z E q‖ ≤ (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2 := by
  obtain ⟨htl, _, hx, hpair⟩ := nuclearChart_closed_geometry t0 ht0 hY hT
  have htp : 0 < ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by
    linarith
  have hpp : 0 < ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖ := by linarith
  have hti : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹ ≤ (4 / 3 : ℝ) := by
    have h := (inv_le_inv₀ htp (by norm_num : (0 : ℝ) < 3 / 4)).mpr htl
    norm_num at h
    exact h
  have hpi : ‖position (nuclearKSLift (0 : Fin 2) q) (0 : Fin 2) -
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2)‖⁻¹ ≤ (16 / 11 : ℝ) := by
    have h := (inv_le_inv₀ hpp (by norm_num : (0 : ℝ) < 11 / 16)).mpr hpair
    norm_num at h
    exact h
  have hV : ‖coulombWithoutSelectedNucleus (0 : Fin 2) Z (nuclearKSLift (0 : Fin 2) q)‖ ≤
      |Z| * (4 / 3 : ℝ) + 16 / 11 := by
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
      |Z| * (4 / 3 : ℝ) + 16 / 11 + |E| := by
    exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs] using add_le_add hV (le_refl ‖E‖))
  have hsq : ‖q.1‖ ^ 2 ≤ (1 / 16 : ℝ) := by
    rwa [nuclearKSLift_nuclear_radius] at hx
  rw [nuclearKSPotential]
  calc
    _ ≤ ‖-8 * Z‖ + ‖8 * ‖q.1‖ ^ 2 *
        (coulombWithoutSelectedNucleus (0 : Fin 2) Z (nuclearKSLift (0 : Fin 2) q) - E)‖ := norm_add_le _ _
    _ = 8 * |Z| + 8 * ‖q.1‖ ^ 2 *
        ‖coulombWithoutSelectedNucleus (0 : Fin 2) Z (nuclearKSLift (0 : Fin 2) q) - E‖ := by
      simp [norm_mul, Real.norm_eq_abs]
    _ ≤ 8 * |Z| + 8 * ‖q.1‖ ^ 2 * (|Z| * (4 / 3 : ℝ) + 16 / 11 + |E|) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hVE (by positivity))
    _ ≤ 8 * |Z| + (1 / 2 : ℝ) * (|Z| * (4 / 3 : ℝ) + 16 / 11 + |E|) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (by nlinarith) (by positivity))
    _ = _ := by ring

theorem nuclearKSPotential_norm_le_of_mem_nuclearChartOpen
    (Z E : ℝ) (t0 : Position) (ht0 : ‖t0‖ = 1) {q : NuclearKSSpace (0 : Fin 2)}
    (hq : q ∈ nuclearChartOpen t0) :
    ‖nuclearKSPotential (0 : Fin 2) Z E q‖ ≤ (26 / 3 : ℝ) * |Z| + 8 / 11 + |E| / 2 :=
  nuclearKSPotential_norm_le_of_closed_chart Z E t0 ht0 hq.1.le hq.2.le

#print axioms nuclearChartOpen_isOpen
#print axioms nuclearChart_closed_geometry
#print axioms nuclearChartOpen_subset_coefficientPatch
#print axioms nuclearKSPotential_norm_le_of_mem_nuclearChartOpen

end ManyBody.S8
