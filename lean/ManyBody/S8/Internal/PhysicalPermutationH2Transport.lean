import ManyBody.S8.Internal.PhysicalHamiltonianResidualBounds
import WeakPermutation_v2

/-! Genuine permutation transport of actual physical weak derivative families.
The state, first derivatives and every ordered second derivative are pulled
back through the original physical permutation. The coordinate labels are
reindexed by the inverse actual coordinate permutation. Lebesgue-measure
preservation gives exact L2 norms, and finite reindexing gives exact equality
of the true two-electron 43-component H2 norm. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalPermutationFirst {N : ℕ} (π : Equiv.Perm (Fin N))
    (d : Coordinate N → SpatialL2 N) : Coordinate N → SpatialL2 N :=
  fun k => pullback π (d ((coordinatePermutation π).symm k))

def physicalPermutationSecond {N : ℕ} (π : Equiv.Perm (Fin N))
    (e : Coordinate N → Coordinate N → SpatialL2 N) :
    Coordinate N → Coordinate N → SpatialL2 N :=
  fun k l => pullback π (e ((coordinatePermutation π).symm k)
    ((coordinatePermutation π).symm l))

theorem physical_permutation_L2_norm {N : ℕ} (π : Equiv.Perm (Fin N))
    (f : SpatialL2 N) : ‖pullback π f‖=‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (permuteSpace π)
    (permuteSpace π).measurePreserving).norm_map f

theorem physical_permutation_weak_families {N : ℕ} (π : Equiv.Perm (Fin N))
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀k,WeakPartial f (d k) k)
    (he : ∀k l,WeakPartial (d k) (e k l) l) :
    (∀k,WeakPartial (pullback π f) (physicalPermutationFirst π d k) k) ∧
    (∀k l,WeakPartial (physicalPermutationFirst π d k)
      (physicalPermutationSecond π e k l) l) ∧
    HasH2 (pullback π f) := by
  have hfirst (k : Coordinate N) :
      WeakPartial (pullback π f) (physicalPermutationFirst π d k) k := by
    simpa only [physicalPermutationFirst,Equiv.apply_symm_apply] using
      weakPartial_pullback π (hd ((coordinatePermutation π).symm k))
  have hsecond (k l : Coordinate N) :
      WeakPartial (physicalPermutationFirst π d k)
        (physicalPermutationSecond π e k l) l := by
    simpa only [physicalPermutationFirst,physicalPermutationSecond,Equiv.apply_symm_apply] using
      weakPartial_pullback π
        (he ((coordinatePermutation π).symm k) ((coordinatePermutation π).symm l))
  refine ⟨hfirst,hsecond,physicalPermutationFirst π d,hfirst,?_⟩
  intro k l
  exact ⟨physicalPermutationSecond π e k l,hsecond k l⟩

theorem physical_permutation_representative_ae {N : ℕ} (π : Equiv.Perm (Fin N))
    {f : SpatialL2 N} {u : Configuration N → ℂ}
    (hu : (f : Configuration N → ℂ)=ᵐ[volume]u) :
    (pullback π f : Configuration N → ℂ)=ᵐ[volume]u∘permuteSpace π := by
  exact (pullback_ae π f).trans
    ((permuteSpace π).measurePreserving.quasiMeasurePreserving.ae hu)

theorem physical_permutation_first_norm_sq_sum {N : ℕ} (π : Equiv.Perm (Fin N))
    (d : Coordinate N → SpatialL2 N) :
    (∑k,‖physicalPermutationFirst π d k‖^2)=(∑k,‖d k‖^2) := by
  simp only [physicalPermutationFirst,physical_permutation_L2_norm]
  exact Equiv.sum_comp (coordinatePermutation π).symm (fun k => ‖d k‖^2)

theorem physical_permutation_second_norm_sq_sum {N : ℕ} (π : Equiv.Perm (Fin N))
    (e : Coordinate N → Coordinate N → SpatialL2 N) :
    (∑k,∑l,‖physicalPermutationSecond π e k l‖^2)=(∑k,∑l,‖e k l‖^2) := by
  simp only [physicalPermutationSecond,physical_permutation_L2_norm]
  calc
    _=(∑k,∑l,‖e ((coordinatePermutation π).symm k) l‖^2) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Equiv.sum_comp (coordinatePermutation π).symm
        (fun l => ‖e ((coordinatePermutation π).symm k) l‖^2)
    _=_ := Equiv.sum_comp (coordinatePermutation π).symm (fun k => ∑l,‖e k l‖^2)

theorem physical_permutation_H2_component_norm (π : Equiv.Perm (Fin 2))
    (f : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) :
    physicalH2ComponentNorm (pullback π f) (physicalPermutationFirst π d)
      (physicalPermutationSecond π e)=physicalH2ComponentNorm f d e := by
  unfold physicalH2ComponentNorm
  rw [physical_permutation_L2_norm,physical_permutation_first_norm_sq_sum,
    physical_permutation_second_norm_sq_sum]

#print axioms physical_permutation_L2_norm
#print axioms physical_permutation_weak_families
#print axioms physical_permutation_representative_ae
#print axioms physical_permutation_H2_component_norm
end ManyBody.S8
