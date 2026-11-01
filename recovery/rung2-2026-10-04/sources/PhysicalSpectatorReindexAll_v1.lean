import PhysicalSpectatorReindex_v1

/-! Exact three-coordinate spectator reindexing for either selected electron
in N=2. The inverse uses the other electron i.rev, with the finite-coordinate
inverse laws proved explicitly. The index-zero map agrees with the sealed
physical pair-center reindexing. No PDE or integral transport is asserted. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def twoElectronSpectatorCoordinateEquiv (i : Fin 2) : SpectatorCoordinate i ≃ Fin 3 where
  toFun k := k.val.2
  invFun k := ⟨(i.rev,k),by change i.rev ≠ i; fin_cases i <;> decide⟩
  left_inv k := by
    apply Subtype.ext
    rcases k with ⟨⟨j,l⟩,hj⟩
    fin_cases i <;> fin_cases j
    · exact False.elim (hj rfl)
    · rfl
    · rfl
    · exact False.elim (hj rfl)
  right_inv k := rfl

def twoElectronSpectatorPositionEquiv (i : Fin 2) :
    SpectatorConfiguration i ≃ₗᵢ[ℝ] Position :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (twoElectronSpectatorCoordinateEquiv i)

theorem twoElectronSpectatorPositionEquiv_apply (i : Fin 2)
    (s : SpectatorConfiguration i) (k : Fin 3) :
    twoElectronSpectatorPositionEquiv i s k =
      s ⟨(i.rev,k),by change i.rev ≠ i; fin_cases i <;> decide⟩ := rfl

theorem twoElectronSpectatorPositionEquiv_symm_apply (i : Fin 2)
    (t : Position) (k : SpectatorCoordinate i) :
    (twoElectronSpectatorPositionEquiv i).symm t k = t k.val.2 := by
  change (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (twoElectronSpectatorCoordinateEquiv i)).symm t k = t k.val.2
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

theorem twoElectronSpectatorPositionEquiv_basis (i : Fin 2) (k : SpectatorCoordinate i) :
    twoElectronSpectatorPositionEquiv i (spectatorBasis k) = ksTargetBasis k.val.2 := by
  change LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (twoElectronSpectatorCoordinateEquiv i)
    (PiLp.single 2 k 1) = PiLp.single 2 (twoElectronSpectatorCoordinateEquiv i k) 1
  exact LinearIsometryEquiv.piLpCongrLeft_single (twoElectronSpectatorCoordinateEquiv i) k 1

theorem twoElectronSpectatorCoordinate_card (i : Fin 2) :
    Fintype.card (SpectatorCoordinate i) = 3 := by
  rw [Fintype.card_congr (twoElectronSpectatorCoordinateEquiv i), Fintype.card_fin]

def physicalSpectatorReindexAt (i : Fin 2) :
    WeakGrushin.Space (SpectatorCoordinate i) ≃ₗᵢ[ℝ] WeakGrushin.Space (Fin 3) where
  toLinearEquiv := (LinearEquiv.refl ℝ KSSpace).prodCongr
    (twoElectronSpectatorPositionEquiv i).toLinearEquiv
  norm_map' q := by
    change max ‖q.1‖ ‖twoElectronSpectatorPositionEquiv i q.2‖ = max ‖q.1‖ ‖q.2‖
    rw [(twoElectronSpectatorPositionEquiv i).norm_map]

theorem physicalSpectatorReindexAt_apply (i : Fin 2)
    (q : WeakGrushin.Space (SpectatorCoordinate i)) :
    physicalSpectatorReindexAt i q = (q.1, twoElectronSpectatorPositionEquiv i q.2) := rfl

theorem physicalSpectatorReindexAt_symm_apply (i : Fin 2) (q : WeakGrushin.Space (Fin 3)) :
    (physicalSpectatorReindexAt i).symm q =
      (q.1, (twoElectronSpectatorPositionEquiv i).symm q.2) := rfl

theorem physicalSpectatorReindexAt_yDir (i : Fin 2) (j : Fin 4) :
    physicalSpectatorReindexAt i (WeakGrushin.yDir j) = WeakGrushin.yDir j := by
  simp only [physicalSpectatorReindexAt_apply, WeakGrushin.yDir, map_zero]

theorem physicalSpectatorReindexAt_tDir (i : Fin 2) (j : SpectatorCoordinate i) :
    physicalSpectatorReindexAt i (WeakGrushin.tDir j) =
      WeakGrushin.tDir (twoElectronSpectatorCoordinateEquiv i j) := by
  change (0, twoElectronSpectatorPositionEquiv i (spectatorBasis j)) = (0, ksTargetBasis j.val.2)
  rw [twoElectronSpectatorPositionEquiv_basis]

theorem physicalSpectatorReindexAt_symm_yDir (i : Fin 2) (j : Fin 4) :
    (physicalSpectatorReindexAt i).symm (WeakGrushin.yDir j) = WeakGrushin.yDir j := by
  apply (physicalSpectatorReindexAt i).injective
  rw [(physicalSpectatorReindexAt i).apply_symm_apply, physicalSpectatorReindexAt_yDir]

theorem physicalSpectatorReindexAt_symm_tDir (i : Fin 2) (j : Fin 3) :
    (physicalSpectatorReindexAt i).symm (WeakGrushin.tDir j) =
      WeakGrushin.tDir ((twoElectronSpectatorCoordinateEquiv i).symm j) := by
  apply (physicalSpectatorReindexAt i).injective
  rw [(physicalSpectatorReindexAt i).apply_symm_apply, physicalSpectatorReindexAt_tDir,
    (twoElectronSpectatorCoordinateEquiv i).apply_symm_apply]

theorem physicalSpectatorReindexAt_contDiff (i : Fin 2) :
    ContDiff ℝ ∞ (physicalSpectatorReindexAt i) := (physicalSpectatorReindexAt i).contDiff

theorem physicalSpectatorReindexAt_symm_contDiff (i : Fin 2) :
    ContDiff ℝ ∞ (physicalSpectatorReindexAt i).symm := (physicalSpectatorReindexAt i).symm.contDiff

def physicalSpectatorHomeomorphAt (i : Fin 2) :
    WeakGrushin.Space (SpectatorCoordinate i) ≃ₜ WeakGrushin.Space (Fin 3) :=
  (physicalSpectatorReindexAt i).toHomeomorph

theorem physicalSpectatorHomeomorphAt_apply (i : Fin 2)
    (q : WeakGrushin.Space (SpectatorCoordinate i)) :
    physicalSpectatorHomeomorphAt i q = physicalSpectatorReindexAt i q := rfl

theorem physicalSpectatorHomeomorphAt_symm_apply (i : Fin 2) (q : WeakGrushin.Space (Fin 3)) :
    (physicalSpectatorHomeomorphAt i).symm q = (physicalSpectatorReindexAt i).symm q := rfl

theorem twoElectronSpectatorPositionEquiv_zero :
    twoElectronSpectatorPositionEquiv (0 : Fin 2) = pairCenterEquiv := rfl

theorem physicalSpectatorReindexAt_zero :
    physicalSpectatorReindexAt (0 : Fin 2) = physicalSpectatorReindex := rfl

end TheoremT.Continuum
