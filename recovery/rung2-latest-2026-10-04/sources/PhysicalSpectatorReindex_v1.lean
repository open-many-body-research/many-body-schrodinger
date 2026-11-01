import WeakGrushinJetFields_v1
import PairKSLift_v1

/-! Exact reindexing of the N=2 spectator coordinates into physical center
three-space. This is a linear isometry for the ordinary product max norm;
it makes no identification of that norm with a product inner-product norm.
No differential equation or integral transport is asserted here. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def physicalSpectatorReindex :
    WeakGrushin.Space (SpectatorCoordinate (0 : Fin 2)) ≃ₗᵢ[ℝ]
      WeakGrushin.Space (Fin 3) where
  toLinearEquiv := (LinearEquiv.refl ℝ KSSpace).prodCongr pairCenterEquiv.toLinearEquiv
  norm_map' q := by
    change max ‖q.1‖ ‖pairCenterEquiv q.2‖ = max ‖q.1‖ ‖q.2‖
    rw [pairCenterEquiv.norm_map]

theorem physicalSpectatorReindex_apply
    (q : WeakGrushin.Space (SpectatorCoordinate (0 : Fin 2))) :
    physicalSpectatorReindex q = (q.1, pairCenterEquiv q.2) := rfl

theorem physicalSpectatorReindex_symm_apply (q : WeakGrushin.Space (Fin 3)) :
    physicalSpectatorReindex.symm q = (q.1, pairCenterEquiv.symm q.2) := rfl

theorem physicalSpectatorReindex_yDir (j : Fin 4) :
    physicalSpectatorReindex (WeakGrushin.yDir j) = WeakGrushin.yDir j := by
  simp only [physicalSpectatorReindex_apply, WeakGrushin.yDir, map_zero]

theorem physicalSpectatorReindex_tDir (j : SpectatorCoordinate (0 : Fin 2)) :
    physicalSpectatorReindex (WeakGrushin.tDir j) =
      WeakGrushin.tDir (pairSpectatorCoordinateEquiv j) := by
  change (0, pairCenterEquiv (spectatorBasis j)) = (0, ksTargetBasis j.val.2)
  rw [pairCenterEquiv_basis]

theorem physicalSpectatorReindex_symm_yDir (j : Fin 4) :
    physicalSpectatorReindex.symm (WeakGrushin.yDir j) = WeakGrushin.yDir j := by
  apply physicalSpectatorReindex.injective
  rw [physicalSpectatorReindex.apply_symm_apply, physicalSpectatorReindex_yDir]

theorem physicalSpectatorReindex_symm_tDir (j : Fin 3) :
    physicalSpectatorReindex.symm (WeakGrushin.tDir j) =
      WeakGrushin.tDir (pairSpectatorCoordinateEquiv.symm j) := by
  apply physicalSpectatorReindex.injective
  rw [physicalSpectatorReindex.apply_symm_apply, physicalSpectatorReindex_tDir,
    pairSpectatorCoordinateEquiv.apply_symm_apply]

theorem physicalSpectatorCoordinate_card :
    Fintype.card (SpectatorCoordinate (0 : Fin 2)) = 3 := by
  rw [Fintype.card_congr pairSpectatorCoordinateEquiv, Fintype.card_fin]

theorem physicalSpectatorReindex_contDiff : ContDiff ℝ ∞ physicalSpectatorReindex :=
  physicalSpectatorReindex.contDiff

theorem physicalSpectatorReindex_symm_contDiff : ContDiff ℝ ∞ physicalSpectatorReindex.symm :=
  physicalSpectatorReindex.symm.contDiff

def physicalSpectatorHomeomorph :
    WeakGrushin.Space (SpectatorCoordinate (0 : Fin 2)) ≃ₜ WeakGrushin.Space (Fin 3) :=
  physicalSpectatorReindex.toHomeomorph

theorem physicalSpectatorHomeomorph_apply
    (q : WeakGrushin.Space (SpectatorCoordinate (0 : Fin 2))) :
    physicalSpectatorHomeomorph q = physicalSpectatorReindex q := rfl

theorem physicalSpectatorHomeomorph_symm_apply (q : WeakGrushin.Space (Fin 3)) :
    physicalSpectatorHomeomorph.symm q = physicalSpectatorReindex.symm q := rfl

end TheoremT.Continuum
