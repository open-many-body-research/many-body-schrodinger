import ManyBody.S8.Internal.PhysicalDistanceCompositionLimits
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
/-! Compact bounds for actual profiles on the literal physical distance images.

The same finite bound controls the value and true first and second Frechet
operator fields of a globally smooth distance profile at every original image
and every positive regularized image with parameter at most one. Compactness
and actual physical coordinate bounds discharge the range and derivative
bounds; no norm bound or regularized-image premise is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ContDiff
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_distance_triple_norm_le (x : Configuration 2) :
    ‖physicalDistanceTriple x‖ ≤ 2 * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  simpa only [physicalDistanceTriple, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    using physical_distance_map_norm_le j x

theorem regularized_physical_distance_triple_norm_le {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (x : Configuration 2) :
    ‖regularizedPhysicalDistanceTriple δ x‖ ≤ 2 * ‖x‖ + 1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change ‖regularizedLinearRadius (physicalDistanceLinearMaps j) δ x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (regularizedLinearRadius_pos _ hδ x)]
  exact (regularizedLinearRadius_le_norm_add_one _ hδ hδ1 x).trans
    (add_le_add (physical_distance_map_norm_le j x) (le_refl 1))

theorem physical_distance_images_compact_ball (K : Set (Configuration 2)) (hK : IsCompact K) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ x ∈ K, physicalDistanceTriple x ∈ closedBall (0 : Fin 3 → ℝ) b) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
        regularizedPhysicalDistanceTriple δ x ∈ closedBall (0 : Fin 3 → ℝ) b := by
  obtain ⟨s, hs⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  let b : ℝ := 2 * max 0 s + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hxbound : ∀ x ∈ K, ‖x‖ ≤ max 0 s :=
    fun x hx => (hs x hx).trans (le_max_right _ _)
  refine ⟨b, hb, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall, dist_zero_right]
    exact (physical_distance_triple_norm_le x).trans (by dsimp [b]; linarith [hxbound x hx])
  · intro δ hδ hδ1 x hx
    rw [mem_closedBall, dist_zero_right]
    exact (regularized_physical_distance_triple_norm_le hδ hδ1 x).trans
      (by dsimp [b]; linarith [hxbound x hx])

theorem physical_distance_profile_compact_bounds
    (K : Set (Configuration 2)) (hK : IsCompact K)
    (g : (Fin 3 → ℝ) → ℂ) (hg : ContDiff ℝ ∞ g) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      (∀ x ∈ K,
        ‖g (physicalDistanceTriple x)‖ ≤ Cg ∧
        ‖fderiv ℝ g (physicalDistanceTriple x)‖ ≤ Cg ∧
        ‖fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)‖ ≤ Cg) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
        ‖g (regularizedPhysicalDistanceTriple δ x)‖ ≤ Cg ∧
        ‖fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)‖ ≤ Cg ∧
        ‖fderiv ℝ (fderiv ℝ g) (regularizedPhysicalDistanceTriple δ x)‖ ≤ Cg := by
  obtain ⟨b, hb, hactual, hregularized⟩ := physical_distance_images_compact_ball K hK
  have hball := isCompact_closedBall (0 : Fin 3 → ℝ) b
  obtain ⟨B0, hB0⟩ := hball.exists_bound_of_continuousOn hg.continuous.continuousOn
  have hD1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)

  obtain ⟨B1, hB1⟩ := hball.exists_bound_of_continuousOn hD1.continuousOn
  have hD2iter : Continuous (iteratedFDeriv ℝ 2 g) := continuous_iff_continuousAt.mpr fun q =>
    hg.contDiffAt.continuousAt_iteratedFDeriv (by simp)
  have hD2norm : Continuous (fun q : Fin 3 → ℝ => ‖fderiv ℝ (fderiv ℝ g) q‖) := by
    have heq : (fun q : Fin 3 → ℝ => ‖fderiv ℝ (fderiv ℝ g) q‖) =
        (fun q : Fin 3 → ℝ => ‖iteratedFDeriv ℝ 2 g q‖) := by
      funext q
      rw [←norm_iteratedFDeriv_one (fderiv ℝ g), norm_iteratedFDeriv_fderiv]
    rw [heq]
    exact hD2iter.norm
  obtain ⟨B2, hB2norm⟩ := hball.exists_bound_of_continuousOn hD2norm.continuousOn
  have hB2 : ∀ q ∈ closedBall (0 : Fin 3 → ℝ) b, ‖fderiv ℝ (fderiv ℝ g) q‖ ≤ B2 := by
    intro q hq
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB2norm q hq)
  let Cg : ℝ := max 0 (max B0 (max B1 B2))
  have hC0 : 0 ≤ Cg := le_max_left _ _
  have hCB0 : B0 ≤ Cg := (le_max_left _ _).trans (le_max_right _ _)
  have hCB1 : B1 ≤ Cg :=
    (le_max_left B1 B2).trans ((le_max_right B0 _).trans (le_max_right _ _))
  have hCB2 : B2 ≤ Cg :=
    (le_max_right B1 B2).trans ((le_max_right B0 _).trans (le_max_right _ _))
  have hbound : ∀ q ∈ closedBall (0 : Fin 3 → ℝ) b,
      ‖g q‖ ≤ Cg ∧ ‖fderiv ℝ g q‖ ≤ Cg ∧ ‖fderiv ℝ (fderiv ℝ g) q‖ ≤ Cg := by
    intro q hq
    exact ⟨(hB0 q hq).trans hCB0, (hB1 q hq).trans hCB1, (hB2 q hq).trans hCB2⟩
  exact ⟨Cg, hC0, fun x hx => hbound _ (hactual x hx),
    fun δ hδ hδ1 x hx => hbound _ (hregularized δ hδ hδ1 x hx)⟩

#print axioms physical_distance_images_compact_ball
#print axioms physical_distance_profile_compact_bounds
end ManyBody.S8
