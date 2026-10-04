import ManyBody.S8.Internal.NuclearChartScaling
import LocalWeakGrushinPlateau_v1

/-!
The actual nuclear charts contain a selected collision point with any prescribed
other-electron position. Smooth compact plateau cutoffs exist there. This uses
literal spectator coordinates, without a spectator-space isometry or a new
physical operator. No quantitative derivative budget for the cutoff is asserted.
-/
noncomputable section
open Filter
open scoped ContDiff Topology
open TheoremT.Continuum

namespace ManyBody.S8

/-- A point of the existing nuclear KS space with zero selected KS coordinate
and the prescribed physical position of the other electron. -/
def nuclearChartCollisionPoint (t0 : Position) : NuclearKSSpace (0 : Fin 2) :=
  (0, WithLp.toLp 2 (fun k : SpectatorCoordinate (0 : Fin 2) => t0 k.val.2))

theorem nuclearChartCollisionPoint_fst (t0 : Position) :
    (nuclearChartCollisionPoint t0).1 = 0 := rfl

theorem nuclearChartCollisionPoint_other_position (t0 : Position) :
    position (nuclearKSLift (0 : Fin 2) (nuclearChartCollisionPoint t0)) (1 : Fin 2) = t0 := by
  ext k
  change configurationReassemble (0 : Fin 2) (ksMap 0)
    (WithLp.toLp 2 (fun j : SpectatorCoordinate (0 : Fin 2) => t0 j.val.2)) (1, k) = t0 k
  exact configurationReassemble_spectator (0 : Fin 2) (ksMap 0)
    (WithLp.toLp 2 (fun j : SpectatorCoordinate (0 : Fin 2) => t0 j.val.2))
    ⟨(1, k), by change (1 : Fin 2) ≠ 0; decide⟩

theorem nuclearChartCollisionPoint_mem_scaledOpen
    (r : ℝ) (hr : 0 < r) (t0 : Position) :
    nuclearChartCollisionPoint t0 ∈ nuclearChartScaledOpen r t0 := by
  change ‖(nuclearChartCollisionPoint t0).1‖ ^ 2 < r / 16 ∧
    ‖position (nuclearKSLift (0 : Fin 2) (nuclearChartCollisionPoint t0)) (1 : Fin 2) - t0‖ < r / 4
  rw [nuclearChartCollisionPoint_fst, nuclearChartCollisionPoint_other_position]
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self]
  constructor <;> positivity

theorem nuclearChartCollisionPoint_mem_open (t0 : Position) :
    nuclearChartCollisionPoint t0 ∈ nuclearChartOpen t0 := by
  change ‖(nuclearChartCollisionPoint t0).1‖ < (1 / 4 : ℝ) ∧
    ‖position (nuclearKSLift (0 : Fin 2) (nuclearChartCollisionPoint t0)) (1 : Fin 2) - t0‖ < (1 / 4 : ℝ)
  rw [nuclearChartCollisionPoint_fst, nuclearChartCollisionPoint_other_position]
  norm_num

theorem nuclearChartScaledOpen_exists_collision_point
    (r : ℝ) (hr : 0 < r) (t0 : Position) (ht0 : ‖t0‖ = r) :
    ∃ q : NuclearKSSpace (0 : Fin 2), q.1 = 0 ∧
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) = t0 ∧
      q ∈ nuclearChartScaledOpen r t0 ∧ q ∈ nuclearKSCoefficientPatch (0 : Fin 2) := by
  have hm := nuclearChartCollisionPoint_mem_scaledOpen r hr t0
  exact ⟨nuclearChartCollisionPoint t0, nuclearChartCollisionPoint_fst t0,
    nuclearChartCollisionPoint_other_position t0, hm,
    nuclearChartScaledOpen_subset_coefficientPatch r hr t0 ht0 hm⟩

theorem nuclearChartOpen_exists_collision_point (t0 : Position) (ht0 : ‖t0‖ = 1) :
    ∃ q : NuclearKSSpace (0 : Fin 2), q.1 = 0 ∧
      position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) = t0 ∧
      q ∈ nuclearChartOpen t0 ∧ q ∈ nuclearKSCoefficientPatch (0 : Fin 2) := by
  have hm := nuclearChartCollisionPoint_mem_open t0
  exact ⟨nuclearChartCollisionPoint t0, nuclearChartCollisionPoint_fst t0,
    nuclearChartCollisionPoint_other_position t0, hm,
    nuclearChartOpen_subset_coefficientPatch t0 ht0 hm⟩

theorem nuclearChartScaledOpen_exists_collision_plateau
    (r : ℝ) (hr : 0 < r) (t0 : Position) :
    ∃ χ : NuclearKSSpace (0 : Fin 2) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ nuclearChartScaledOpen r t0 ∧
      ∃ V : Set (NuclearKSSpace (0 : Fin 2)), IsOpen V ∧
        nuclearChartCollisionPoint t0 ∈ V ∧ V ⊆ nuclearChartScaledOpen r t0 ∧
        ∀ p ∈ V, χ p = 1 := by
  have hm := nuclearChartCollisionPoint_mem_scaledOpen r hr t0
  have hs : ({nuclearChartCollisionPoint t0} : Set (NuclearKSSpace (0 : Fin 2))) ⊆
      nuclearChartScaledOpen r t0 := Set.singleton_subset_iff.mpr hm
  obtain ⟨χ, hχ, hcχ, hsχ, V, hV, hqV, hVO, hχ1⟩ :=
    WeakGrushin.exists_outer_plateau (κ := SpectatorCoordinate (0 : Fin 2))
      isCompact_singleton (nuclearChartScaledOpen_isOpen r t0) hs
  exact ⟨χ, hχ, hcχ, hsχ, V, hV, hqV (Set.mem_singleton _), hVO, hχ1⟩

theorem nuclearChartOpen_exists_collision_plateau (t0 : Position) :
    ∃ χ : NuclearKSSpace (0 : Fin 2) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ nuclearChartOpen t0 ∧
      ∃ V : Set (NuclearKSSpace (0 : Fin 2)), IsOpen V ∧
        nuclearChartCollisionPoint t0 ∈ V ∧ V ⊆ nuclearChartOpen t0 ∧
        ∀ p ∈ V, χ p = 1 := by
  have hm := nuclearChartCollisionPoint_mem_open t0
  have hs : ({nuclearChartCollisionPoint t0} : Set (NuclearKSSpace (0 : Fin 2))) ⊆
      nuclearChartOpen t0 := Set.singleton_subset_iff.mpr hm
  obtain ⟨χ, hχ, hcχ, hsχ, V, hV, hqV, hVO, hχ1⟩ :=
    WeakGrushin.exists_outer_plateau (κ := SpectatorCoordinate (0 : Fin 2))
      isCompact_singleton (nuclearChartOpen_isOpen t0) hs
  exact ⟨χ, hχ, hcχ, hsχ, V, hV, hqV (Set.mem_singleton _), hVO, hχ1⟩

#print axioms nuclearChartCollisionPoint_other_position
#print axioms nuclearChartScaledOpen_exists_collision_point
#print axioms nuclearChartOpen_exists_collision_point
#print axioms nuclearChartScaledOpen_exists_collision_plateau
#print axioms nuclearChartOpen_exists_collision_plateau

end ManyBody.S8
