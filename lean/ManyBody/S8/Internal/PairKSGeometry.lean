import TwoElectronRelativeSobolev_v1
import NuclearKSPotentialSmooth_v1
import CoulombTwoElectronExpectation_v1

/-! Electron-pair KS geometry reconstructs the original two-electron positions
from the orthogonal center/relative coordinates. The selected relative coordinate
is the second three-vector, and its Coulomb denominator carries sqrt(2).
The coefficient patch retains the selected pair collision and excludes both nuclei. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace ManyBody.S8
open TheoremT.Continuum

abbrev PairKSSpace := NuclearKSSpace (1 : Fin 2)

def pairKSLift (q : PairKSSpace) : Configuration 2 :=
  twoElectronRelativeEquiv (nuclearKSLift (1 : Fin 2) q)

theorem pairKSLift_contDiff : ContDiff ℝ ∞ pairKSLift :=
  twoElectronRelativeEquiv.toContinuousLinearEquiv.contDiff.comp
    (nuclearKSLift_contDiff (1 : Fin 2))

theorem pairKSLift_locallyLipschitz : LocallyLipschitz pairKSLift :=
  (pairKSLift_contDiff.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz

theorem relative_apply_twice (x : Configuration 2) :
    twoElectronRelativeEquiv (twoElectronRelativeEquiv x) = x :=
  twoElectronHadamard_involutive x

theorem relative_original_first (x : Configuration 2) :
    position (twoElectronRelativeEquiv x) (0 : Fin 2) =
      (Real.sqrt 2)⁻¹ • (position x 0 + position x 1) := by
  apply (WithLp.ext_iff 2).mpr
  funext k
  change twoElectronHadamardLinear x (0,k) =
    (Real.sqrt 2)⁻¹ * (x (0,k)+x (1,k))
  rw [twoElectronHadamard_first]
  ring

theorem pairKSLift_first_position (q : PairKSSpace) :
    position (pairKSLift q) (0 : Fin 2) = (Real.sqrt 2)⁻¹ •
      (position (nuclearKSLift (1 : Fin 2) q) 0 + ksMap q.1) := by
  rw [pairKSLift,relative_original_first,nuclearKSLift_selected_position]

theorem pairKSLift_second_position (q : PairKSSpace) :
    position (pairKSLift q) (1 : Fin 2) = (Real.sqrt 2)⁻¹ •
      (position (nuclearKSLift (1 : Fin 2) q) 0 - ksMap q.1) := by
  rw [pairKSLift,twoElectronRelativeEquiv_pair_position,nuclearKSLift_selected_position]

theorem pairKSLift_pair_radius (q : PairKSSpace) :
    ‖position (pairKSLift q) 0-position (pairKSLift q) 1‖ =
      Real.sqrt 2 * ‖q.1‖^2 := by
  rw [twoElectronRelativeEquiv_pair_norm,pairKSLift,relative_apply_twice,
    nuclearKSLift_nuclear_radius]

def pairKSCoefficientPatch : Set PairKSSpace :=
  {q | ∀ j : Fin 2, position (pairKSLift q) j ≠ 0}

def pairKSPotential (Z E : ℝ) (q : PairKSSpace) : ℝ :=
  8 / Real.sqrt 2 + 8*‖q.1‖^2 *
    (-Z*(‖position (pairKSLift q) 0‖⁻¹+‖position (pairKSLift q) 1‖⁻¹)-E)

theorem pairKSPotential_eq_coulomb_scaled (Z E : ℝ) (q : PairKSSpace)
    (hq : q.1 ≠ 0) :
    pairKSPotential Z E q =
      8*‖q.1‖^2*(coulombPotential 2 Z (pairKSLift q)-E) := by
  rw [coulombPotential_two_electrons,pairKSLift_pair_radius]
  dsimp [pairKSPotential]
  field_simp [norm_ne_zero_iff.mpr hq,
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  ring

theorem pairKSPotential_on_zero (Z E : ℝ) (t : SpectatorConfiguration (1 : Fin 2)) :
    pairKSPotential Z E (0,t) = 8/Real.sqrt 2 := by simp [pairKSPotential]

theorem pairKSCoefficientPatch_off_zero_collisionFree {q : PairKSSpace}
    (hq : q ∈ pairKSCoefficientPatch) (hy : q.1 ≠ 0) :
    collisionFree (pairKSLift q) := by
  refine ⟨hq,?_⟩
  intro j k hjk
  have hnorm : 0 < ‖position (pairKSLift q) 0-position (pairKSLift q) 1‖ := by
    rw [pairKSLift_pair_radius]
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (sq_pos_of_pos (norm_pos_iff.mpr hy))
  have h01 : position (pairKSLift q) 0 ≠ position (pairKSLift q) 1 :=
    sub_ne_zero.mp (norm_pos_iff.mp hnorm)
  fin_cases j <;> fin_cases k
  · exact (hjk rfl).elim
  · exact h01
  · exact h01.symm
  · exact (hjk rfl).elim

theorem pairKSCoefficientPatch_isOpen : IsOpen pairKSCoefficientPatch := by
  simp only [pairKSCoefficientPatch,Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact (isClosed_eq ((continuous_position j).comp pairKSLift_contDiff.continuous)
    continuous_const).isOpen_compl

theorem pairKSPotential_contDiffAt (Z E : ℝ) {q : PairKSSpace}
    (hq : q ∈ pairKSCoefficientPatch) : ContDiffAt ℝ ∞ (pairKSPotential Z E) q := by
  have hc (j : Fin 2) : ContDiffAt ℝ ∞ (fun q : PairKSSpace => position (pairKSLift q) j) q :=
    (electronPositionCLM j).contDiff.contDiffAt.comp q pairKSLift_contDiff.contDiffAt
  have hn (j : Fin 2) : ContDiffAt ℝ ∞
      (fun q : PairKSSpace => ‖position (pairKSLift q) j‖⁻¹) q :=
    ((hc j).norm ℝ (hq j)).inv (norm_ne_zero_iff.mpr (hq j))
  have hr : ContDiff ℝ ∞ (fun q : PairKSSpace => ‖q.1‖^2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  exact contDiffAt_const.add ((contDiffAt_const.mul hr.contDiffAt).mul
    ((contDiffAt_const.mul ((hn 0).add (hn 1))).sub contDiffAt_const))

#print axioms pairKSLift_pair_radius
#print axioms pairKSPotential_eq_coulomb_scaled
#print axioms pairKSCoefficientPatch_off_zero_collisionFree
#print axioms pairKSPotential_contDiffAt

/-- Every physical isolated pair collision is represented at Y=0 in this chart. -/
theorem pairKSLift_covers_isolated_pair_collision (x : Configuration 2)
    (hpair : position x 0 = position x 1)
    (hnuc : ∀ j : Fin 2, position x j ≠ 0) :
    ∃ q : PairKSSpace, q.1=0 ∧ pairKSLift q=x ∧ q ∈ pairKSCoefficientPatch := by
  let z := twoElectronRelativeEquiv x
  have hz : position z (1 : Fin 2) = 0 := by
    rw [twoElectronRelativeEquiv_pair_position,hpair,sub_self,smul_zero]
  let q : PairKSSpace := (0,((configurationProductEquiv (1 : Fin 2)) z).2)
  have hl : nuclearKSLift (1 : Fin 2) q = z := by
    apply (configurationProductEquiv (1 : Fin 2)).injective
    rw [nuclearKSLift,(configurationProductEquiv (1 : Fin 2)).apply_symm_apply]
    change (ksMap 0,((configurationProductEquiv (1 : Fin 2)) z).2) =
      (configurationProductEquiv (1 : Fin 2)) z
    have h0 : ksMap (0 : KSSpace) = 0 := (ksMap_eq_zero_iff _).mpr rfl
    rw [h0]
    change position z (1 : Fin 2) = _ at hz
    apply Prod.ext
    · change (0 : Position) = position z (1 : Fin 2)
      exact hz.symm
    · rfl
  have he : pairKSLift q = x := by
    rw [pairKSLift,hl]
    exact relative_apply_twice x
  refine ⟨q,rfl,he,?_⟩
  intro j
  rw [he]
  exact hnuc j

#print axioms pairKSLift_covers_isolated_pair_collision
end ManyBody.S8