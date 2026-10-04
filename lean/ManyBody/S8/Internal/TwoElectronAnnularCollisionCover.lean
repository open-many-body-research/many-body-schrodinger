import TwoElectronRelativeCoordinates_v1
import CollisionFreeCutoff_v1
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! A finite cover of the actual two-electron unit annulus by collision-free
points and physical nuclear/pair neighborhoods. The pair center is the original
half-sum coordinate. This is geometric coverage, not an analytic estimate.
-/
noncomputable section
open Set Metric
namespace ManyBody.S8
open TheoremT.Continuum

abbrev PhysicalUnitCenter := {t : Position // ‖t‖ = 1}

def annularPairCenter (x : Configuration 2) : Position :=
  (1 / 2 : ℝ) • (position x 0 + position x 1)

def annularNuclearNeighborhood (i : Fin 2) (t : Position) (η : ℝ) :
    Set (Configuration 2) :=
  {x | ‖position x i‖ < η ∧ ‖position x (1-i) - t‖ < η}

def annularPairNeighborhood (t : Position) (η : ℝ) : Set (Configuration 2) :=
  {x | ‖position x 0 - position x 1‖ < η ∧
    ‖annularPairCenter x - (Real.sqrt 2)⁻¹ • t‖ < η}

def annularPhysicalChartCover (η : ℝ) (t : PhysicalUnitCenter) : Set (Configuration 2) :=
  {x | collisionFree x} ∪ annularNuclearNeighborhood 0 t η ∪
    annularNuclearNeighborhood 1 t η ∪ annularPairNeighborhood t η

theorem configuration_two_position_norm_sq (x : Configuration 2) :
    ‖x‖ ^ 2 = ‖position x 0‖ ^ 2 + ‖position x 1‖ ^ 2 := by
  rw [configuration_two_norm_sq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp only [position, Finset.sum_add_distrib]

theorem annularNuclearNeighborhood_isOpen (i : Fin 2) (t : Position) (η : ℝ) :
    IsOpen (annularNuclearNeighborhood i t η) :=
  (isOpen_lt (continuous_position i).norm continuous_const).inter
    (isOpen_lt ((continuous_position (1-i)).sub continuous_const).norm continuous_const)

theorem annularPairNeighborhood_isOpen (t : Position) (η : ℝ) :
    IsOpen (annularPairNeighborhood t η) := by
  have hc : Continuous annularPairCenter :=
    ((continuous_position 0).add (continuous_position 1)).const_smul (1 / 2 : ℝ)
  exact (isOpen_lt ((continuous_position 0).sub (continuous_position 1)).norm continuous_const).inter
    (isOpen_lt (hc.sub continuous_const).norm continuous_const)

theorem annularPhysicalChartCover_isOpen (η : ℝ) (t : PhysicalUnitCenter) :
    IsOpen (annularPhysicalChartCover η t) :=
  (((collisionFree_isOpen 2).union (annularNuclearNeighborhood_isOpen 0 t η)).union
    (annularNuclearNeighborhood_isOpen 1 t η)).union (annularPairNeighborhood_isOpen t η)

theorem two_electron_unit_annulus_covered {η : ℝ} (hη : 0 < η)
    (x : Configuration 2) (hx : ‖x‖ = 1) :
    ∃ t : PhysicalUnitCenter, x ∈ annularPhysicalChartCover η t := by
  have hnorm := configuration_two_position_norm_sq x
  rw [hx] at hnorm
  by_cases h0 : position x 0 = 0
  · have ht : ‖position x 1‖ = 1 := by rw [h0, norm_zero] at hnorm; nlinarith [norm_nonneg (position x 1)]
    refine ⟨⟨position x 1, ht⟩, ?_⟩
    apply Or.inl
    apply Or.inl
    apply Or.inr
    simp only [annularNuclearNeighborhood, Set.mem_ofPred_eq, h0, norm_zero,
      show (1-(0 : Fin 2))=1 by decide, sub_self]
    exact ⟨hη, hη⟩
  by_cases h1 : position x 1 = 0
  · have ht : ‖position x 0‖ = 1 := by rw [h1, norm_zero] at hnorm; nlinarith [norm_nonneg (position x 0)]
    refine ⟨⟨position x 0, ht⟩, ?_⟩
    apply Or.inl
    apply Or.inr
    simp only [annularNuclearNeighborhood, Set.mem_ofPred_eq, h1, norm_zero,
      show (1-(1 : Fin 2))=0 by decide, sub_self]
    exact ⟨hη, hη⟩
  by_cases hp : position x 0 = position x 1
  · let t : Position := Real.sqrt 2 • position x 0
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have ht : ‖t‖ = 1 := by
      have ht2 : ‖t‖^2 = 1 := by
        rw [← hp] at hnorm
        calc
          _ = 2 * ‖position x 0‖^2 := by simp only [t, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, hsq]
          _ = 1 := by nlinarith
      nlinarith [norm_nonneg t]
    have hc : annularPairCenter x = position x 0 := by
      dsimp [annularPairCenter]
      rw [← hp]
      module
    have he : (Real.sqrt 2)⁻¹ • t = position x 0 := by
      simp only [t, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    refine ⟨⟨t, ht⟩, Or.inr ?_⟩
    change ‖position x 0 - position x 1‖ < η ∧ ‖annularPairCenter x - (Real.sqrt 2)⁻¹ • t‖ < η
    rw [hp, hc, he, sub_self, norm_zero, sub_self, norm_zero]
    exact ⟨hη, hη⟩
  have hregular : collisionFree x := by
    constructor
    · intro i
      fin_cases i <;> assumption
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact hp
      · exact Ne.symm hp
      · exact False.elim (hij rfl)
  let t : Position := ‖position x 0‖⁻¹ • position x 0
  have ht : ‖t‖ = 1 := by
    simp only [t, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
  exact ⟨⟨t, ht⟩, Or.inl (Or.inl (Or.inl hregular))⟩

theorem two_electron_unit_annulus_finite_physical_chart_cover {η : ℝ} (hη : 0 < η) :
    ∃ centers : Finset PhysicalUnitCenter,
      {x : Configuration 2 | ‖x‖ = 1} ⊆ ⋃ t ∈ centers, annularPhysicalChartCover η t := by
  have hs : IsCompact {x : Configuration 2 | ‖x‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : Configuration 2) 1
  apply hs.elim_finite_subcover (annularPhysicalChartCover η)
    (annularPhysicalChartCover_isOpen η)
  intro x hx
  obtain ⟨t, ht⟩ := two_electron_unit_annulus_covered hη x hx
  exact Set.mem_iUnion.mpr ⟨t, ht⟩


theorem annularNuclearNeighborhood_avoids_other_collisions
    (i : Fin 2) (t : Position) (ht : ‖t‖ = 1) {η : ℝ} (hη : η ≤ 1/16)
    {x : Configuration 2} (hx : x ∈ annularNuclearNeighborhood i t η) :
    position x (1-i) ≠ 0 ∧ position x i ≠ position x (1-i) := by
  have hlo : 1-η < ‖position x (1-i)‖ := by
    have hh := norm_sub_norm_le t (position x (1-i))
    rw [ht, norm_sub_rev] at hh
    linarith [hx.2]
  constructor
  · intro hz
    rw [hz,norm_zero] at hlo
    linarith
  · intro he
    have hh := hx.1
    rw [he] at hh
    linarith

theorem annularPairNeighborhood_avoids_nuclear_collisions
    (t : Position) (ht : ‖t‖ = 1) {η : ℝ} (hη : η ≤ 1/16)
    {x : Configuration 2} (hx : x ∈ annularPairNeighborhood t η) :
    ∀ j : Fin 2, position x j ≠ 0 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hi : (1/2 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by
    have hupper : Real.sqrt 2 ≤ 2 := by nlinarith
    have hmul := mul_nonneg (show 0 ≤ 2-Real.sqrt 2 by linarith) (inv_nonneg.mpr hs.le)
    have he := mul_inv_cancel₀ hs.ne'
    nlinarith
  have htarg : ‖(Real.sqrt 2)⁻¹ • t‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_smul, ht, mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hlo : (Real.sqrt 2)⁻¹-η < ‖annularPairCenter x‖ := by
    have hh := norm_sub_norm_le ((Real.sqrt 2)⁻¹ • t) (annularPairCenter x)
    rw [htarg, norm_sub_rev] at hh
    linarith [hx.2]
  have h0 : annularPairCenter x - position x 0 =
      (-1/2 : ℝ) • (position x 0 - position x 1) := by dsimp [annularPairCenter]; module
  have h1 : annularPairCenter x - position x 1 =
      (1/2 : ℝ) • (position x 0 - position x 1) := by dsimp [annularPairCenter]; module
  intro j hj
  fin_cases j
  · have hd : ‖annularPairCenter x - position x 0‖ < η/2 := by
      rw [h0, norm_smul, Real.norm_eq_abs]
      norm_num
      linarith [hx.1]
    change position x 0 = 0 at hj
    rw [hj, sub_zero] at hd
    linarith
  · have hd : ‖annularPairCenter x - position x 1‖ < η/2 := by
      rw [h1, norm_smul, Real.norm_eq_abs]
      norm_num
      linarith [hx.1]
    change position x 1 = 0 at hj
    rw [hj, sub_zero] at hd
    linarith

def scaledAnnularPhysicalChartCover (ρ η : ℝ) (t : PhysicalUnitCenter) :
    Set (Configuration 2) := {x | ρ⁻¹ • x ∈ annularPhysicalChartCover η t}

/-- One finite family of centers works on every nonzero physical radius. -/
theorem two_electron_all_radii_finite_physical_chart_cover {η : ℝ} (hη : 0 < η) :
    ∃ centers : Finset PhysicalUnitCenter, ∀ ρ : ℝ, 0 < ρ →
      {x : Configuration 2 | ‖x‖ = ρ} ⊆
        ⋃ t ∈ centers, scaledAnnularPhysicalChartCover ρ η t := by
  obtain ⟨centers, hcover⟩ := two_electron_unit_annulus_finite_physical_chart_cover hη
  refine ⟨centers, ?_⟩
  intro ρ hρ x hx
  have hn : ‖ρ⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), hx,
      inv_mul_cancel₀ hρ.ne']
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hcover hn)
  obtain ⟨hmem, hpoint⟩ := Set.mem_iUnion.mp ht
  exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨hmem, hpoint⟩⟩

/-- The common scaled chart family covers every configuration except the triple origin. -/
theorem two_electron_punctured_configuration_finite_physical_chart_cover
    {η : ℝ} (hη : 0 < η) :
    ∃ centers : Finset PhysicalUnitCenter, ∀ x : Configuration 2, x ≠ 0 →
      x ∈ ⋃ t ∈ centers, scaledAnnularPhysicalChartCover ‖x‖ η t := by
  obtain ⟨centers, hcover⟩ := two_electron_all_radii_finite_physical_chart_cover hη
  refine ⟨centers, ?_⟩
  intro x hx
  exact hcover ‖x‖ (norm_pos_iff.mpr hx) rfl

#print axioms configuration_two_position_norm_sq
#print axioms two_electron_unit_annulus_covered
#print axioms two_electron_unit_annulus_finite_physical_chart_cover
#print axioms annularNuclearNeighborhood_avoids_other_collisions
#print axioms annularPairNeighborhood_avoids_nuclear_collisions
#print axioms two_electron_all_radii_finite_physical_chart_cover
#print axioms two_electron_punctured_configuration_finite_physical_chart_cover
end ManyBody.S8
