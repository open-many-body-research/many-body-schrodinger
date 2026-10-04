import NuclearKSLift_v1
import SpectatorInsertion_v1

/-! The actual N=2 pair KS chart. Its spectator Euclidean three-space is
identified isometrically with the physical center coordinate t. The two
positions are t+KS(y)/2 and t-KS(y)/2; no orthogonal sqrt(2) convention is used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

abbrev PairKSSpace := NuclearKSSpace (0 : Fin 2)

def pairSpectatorCoordinateEquiv : SpectatorCoordinate (0 : Fin 2) ≃ Fin 3 where
  toFun k := k.val.2
  invFun k := ⟨(1,k),by norm_num⟩
  left_inv k := by
    apply Subtype.ext
    rcases k with ⟨⟨i,l⟩,hi⟩
    fin_cases i
    · exact False.elim (hi rfl)
    · rfl
  right_inv k := rfl

def pairCenterEquiv : SpectatorConfiguration (0 : Fin 2) ≃ₗᵢ[ℝ] Position :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ pairSpectatorCoordinateEquiv

@[simp] theorem pairCenterEquiv_apply (s : SpectatorConfiguration (0 : Fin 2)) (k : Fin 3) :
    pairCenterEquiv s k = s ⟨(1,k),by norm_num⟩ := rfl

theorem pairCenterEquiv_basis (k : SpectatorCoordinate (0 : Fin 2)) :
    pairCenterEquiv (spectatorBasis k) = ksTargetBasis k.val.2 := by
  change LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ pairSpectatorCoordinateEquiv
    (PiLp.single 2 k 1) = PiLp.single 2 (pairSpectatorCoordinateEquiv k) 1
  exact LinearIsometryEquiv.piLpCongrLeft_single pairSpectatorCoordinateEquiv k 1

theorem pairCenterEquiv_measurePreserving : MeasurePreserving pairCenterEquiv :=
  pairCenterEquiv.measurePreserving

def pairCoordinatesLinear : Position × SpectatorConfiguration (0 : Fin 2) →ₗ[ℝ] Configuration 2 where
  toFun q := WithLp.toLp 2 (fun k =>
    pairCenterEquiv q.2 k.2 + if k.1=0 then q.1 k.2/2 else -(q.1 k.2/2))
  map_add' q r := by
    apply (WithLp.ext_iff 2).mpr
    funext ⟨i,k⟩
    fin_cases i <;> simp <;> ring
  map_smul' a q := by
    apply (WithLp.ext_iff 2).mpr
    funext ⟨i,k⟩
    fin_cases i <;> simp <;> ring

def pairCoordinates : Position × SpectatorConfiguration (0 : Fin 2) →L[ℝ] Configuration 2 :=
  pairCoordinatesLinear.toContinuousLinearMap

theorem pairCoordinates_first (q : Position × SpectatorConfiguration (0 : Fin 2)) :
    position (pairCoordinates q) 0 = pairCenterEquiv q.2 + (1/2 : ℝ) • q.1 := by
  ext k
  change pairCenterEquiv q.2 k + q.1 k/2 = pairCenterEquiv q.2 k + (1/2 : ℝ)*q.1 k
  ring

theorem pairCoordinates_second (q : Position × SpectatorConfiguration (0 : Fin 2)) :
    position (pairCoordinates q) 1 = pairCenterEquiv q.2 - (1/2 : ℝ) • q.1 := by
  ext k
  change pairCenterEquiv q.2 k + -(q.1 k/2) = pairCenterEquiv q.2 k - (1/2 : ℝ)*q.1 k
  ring

theorem pairCoordinates_first_basis (k : Fin 3) :
    pairCoordinates (ksTargetBasis k,0) =
      (1/2 : ℝ) • coordinateVector (0,k) - (1/2 : ℝ) • coordinateVector (1,k) := by
  ext ⟨i,l⟩
  fin_cases i <;> simp [pairCoordinates,pairCoordinatesLinear,ksTargetBasis,
    coordinateVector,PiLp.single_apply,Pi.single_apply] <;> split_ifs <;> norm_num

theorem pairCoordinates_spectator_basis (k : SpectatorCoordinate (0 : Fin 2)) :
    pairCoordinates (0,spectatorBasis k) =
      coordinateVector (0,k.val.2) + coordinateVector (1,k.val.2) := by
  ext ⟨i,l⟩
  change pairCenterEquiv (spectatorBasis k) l +
      (if i=0 then (0 : Position) l/2 else -((0 : Position) l/2)) = _
  rw [pairCenterEquiv_basis]
  fin_cases i <;> simp [ksTargetBasis,coordinateVector,PiLp.single_apply,Pi.single_apply]

def pairKSLift (q : PairKSSpace) : Configuration 2 := pairCoordinates (ksMap q.1,q.2)

theorem pairKSLift_contDiff : ContDiff ℝ ∞ pairKSLift :=
  pairCoordinates.contDiff.comp ((ksMap_contDiff.comp contDiff_fst).prodMk contDiff_snd)

theorem pairKSLift_locallyLipschitz : LocallyLipschitz pairKSLift :=
  (pairKSLift_contDiff.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz

theorem pairKSLift_first (q : PairKSSpace) :
    position (pairKSLift q) 0 = pairCenterEquiv q.2 + (1/2 : ℝ) • ksMap q.1 :=
  pairCoordinates_first (ksMap q.1,q.2)

theorem pairKSLift_second (q : PairKSSpace) :
    position (pairKSLift q) 1 = pairCenterEquiv q.2 - (1/2 : ℝ) • ksMap q.1 :=
  pairCoordinates_second (ksMap q.1,q.2)

theorem pairKSLift_difference (q : PairKSSpace) :
    position (pairKSLift q) 0 - position (pairKSLift q) 1 = ksMap q.1 := by
  rw [pairKSLift_first,pairKSLift_second]
  module

theorem pairKSLift_pair_radius (q : PairKSSpace) :
    ‖position (pairKSLift q) 0 - position (pairKSLift q) 1‖ = ‖q.1‖^2 := by
  rw [pairKSLift_difference,ksMap_norm]

#print axioms pairCenterEquiv_basis
#print axioms pairCenterEquiv_measurePreserving
#print axioms pairCoordinates_first_basis
#print axioms pairCoordinates_spectator_basis
#print axioms pairKSLift_contDiff
#print axioms pairKSLift_first
#print axioms pairKSLift_second
#print axioms pairKSLift_difference
#print axioms pairKSLift_pair_radius
end TheoremT.Continuum
