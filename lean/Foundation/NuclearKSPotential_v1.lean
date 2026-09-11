import NuclearKSLift_v1
import CoulombPotentialSmoothAway_v1

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

def coulombWithoutSelectedNucleus {N : ℕ} (i : Fin N) (Z : ℝ) (x : Configuration N) : ℝ :=
  -Z*(∑ j ∈ Finset.univ.erase i, ‖position x j‖⁻¹) +
    ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
      ‖position x j-position x k‖⁻¹

def nuclearKSPotential {N : ℕ} (i : Fin N) (Z E : ℝ) (q : NuclearKSSpace i) : ℝ :=
  -8*Z+8*‖q.1‖^2*(coulombWithoutSelectedNucleus i Z (nuclearKSLift i q)-E)

def nuclearKSCoefficientPatch {N : ℕ} (i : Fin N) : Set (NuclearKSSpace i) :=
  {q | (∀ j : Fin N, j ≠ i → position (nuclearKSLift i q) j ≠ 0) ∧
    ∀ j k : Fin N, j ≠ k → position (nuclearKSLift i q) j ≠ position (nuclearKSLift i q) k}

theorem coulomb_split_selected_nucleus {N : ℕ} (i : Fin N) (Z : ℝ) (x : Configuration N) :
    coulombPotential N Z x = -Z*‖position x i‖⁻¹+coulombWithoutSelectedNucleus i Z x := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (f := fun j : Fin N => ‖position x j‖⁻¹)
    (Finset.mem_univ i)
  simp only [coulombPotential,coulombWithoutSelectedNucleus]
  rw [← hs]
  ring

theorem nuclearKSPotential_eq_coulomb_scaled {N : ℕ} (i : Fin N) (Z E : ℝ)
    (q : NuclearKSSpace i) (hq : q.1 ≠ 0) :
    nuclearKSPotential i Z E q=8*‖q.1‖^2*(coulombPotential N Z (nuclearKSLift i q)-E) := by
  rw [coulomb_split_selected_nucleus i,nuclearKSLift_nuclear_radius]
  dsimp [nuclearKSPotential]
  field_simp [norm_ne_zero_iff.mpr hq]
  <;> ring

theorem nuclearKSPotential_on_zero {N : ℕ} (i : Fin N) (Z E : ℝ)
    (s : SpectatorConfiguration i) : nuclearKSPotential i Z E (0,s) = -8*Z := by
  simp [nuclearKSPotential]

theorem nuclearKSCoefficientPatch_off_zero_collisionFree {N : ℕ} (i : Fin N)
    {q : NuclearKSSpace i} (hq : q ∈ nuclearKSCoefficientPatch i) (hy : q.1 ≠ 0) :
    collisionFree (nuclearKSLift i q) := by
  refine ⟨?_,hq.2⟩
  intro j
  by_cases hj : j=i
  · subst j
    rw [nuclearKSLift_selected_position]
    exact (ksMap_eq_zero_iff q.1).not.mpr hy
  · exact hq.1 j hj

#print axioms nuclearKSPotential_eq_coulomb_scaled
#print axioms nuclearKSPotential_on_zero
#print axioms nuclearKSCoefficientPatch_off_zero_collisionFree
end TheoremT.Continuum
