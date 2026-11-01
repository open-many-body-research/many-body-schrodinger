import PairKSLift_v1
import SecondDirectionalLinearAt_v1
import HardyLaplacianCore_v1

/-! The exact weighted Hessian trace in the unnormalized pair/center chart.
Its factors are 4 on the relative trace and 1 on the center trace, yielding
2 times the physical six-dimensional Laplacian. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem pair_coordinates_bilinear_trace
    (B : Configuration 2 →L[ℝ] Configuration 2 →L[ℝ] ℂ) :
    (4 : ℝ) • (∑ k : Fin 3, B (pairCoordinates (ksTargetBasis k,0))
      (pairCoordinates (ksTargetBasis k,0))) +
    (∑ k : SpectatorCoordinate (0 : Fin 2), B (pairCoordinates (0,spectatorBasis k))
      (pairCoordinates (0,spectatorBasis k))) =
      (2 : ℝ) • ∑ k : Coordinate 2, B (coordinateVector k) (coordinateVector k) := by
  simp_rw [pairCoordinates_first_basis,pairCoordinates_spectator_basis]
  have hs : (∑ k : SpectatorCoordinate (0 : Fin 2),
      B (coordinateVector (0,k.val.2)+coordinateVector (1,k.val.2))
        (coordinateVector (0,k.val.2)+coordinateVector (1,k.val.2))) =
      ∑ k : Fin 3, B (coordinateVector (0,k)+coordinateVector (1,k))
        (coordinateVector (0,k)+coordinateVector (1,k)) :=
    pairSpectatorCoordinateEquiv.sum_comp (fun k : Fin 3 =>
      B (coordinateVector (0,k)+coordinateVector (1,k))
        (coordinateVector (0,k)+coordinateVector (1,k)))
  rw [hs,Finset.smul_sum,← Finset.sum_add_distrib]
  calc
    _ = ∑ k : Fin 3, ((2 : ℝ) • B (coordinateVector (0,k)) (coordinateVector (0,k)) +
        (2 : ℝ) • B (coordinateVector (1,k)) (coordinateVector (1,k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [map_sub,map_smul,sub_apply,ContinuousLinearMap.smul_apply,map_add,add_apply]
      module
    _ = _ := by
      simp only [Coordinate,Fintype.sum_prod_type,Fin.sum_univ_two,
        smul_add,Finset.smul_sum,Finset.sum_add_distrib]

theorem pair_coordinates_weighted_laplacian
    {g : Configuration 2 → ℂ} (q : Position × SpectatorConfiguration (0 : Fin 2))
    (hg : ContDiffAt ℝ 2 g (pairCoordinates q)) :
    (4 : ℝ) • (∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ (g ∘ pairCoordinates) z
      (ksTargetBasis k,0)) q (ksTargetBasis k,0)) +
    (∑ k : SpectatorCoordinate (0 : Fin 2), fderiv ℝ (fun z => fderiv ℝ
      (g ∘ pairCoordinates) z (0,spectatorBasis k)) q (0,spectatorBasis k)) =
      (2 : ℝ) • smoothLaplacian g (pairCoordinates q) := by
  have hd (v : Position × SpectatorConfiguration (0 : Fin 2)) :
      fderiv ℝ (fun z => fderiv ℝ (g ∘ pairCoordinates) z v) q v =
        fderiv ℝ (fun z => fderiv ℝ g z (pairCoordinates v))
          (pairCoordinates q) (pairCoordinates v) :=
    second_directional_linear_at pairCoordinates q v v hg
  simp_rw [hd]
  change _ = (2 : ℝ) • ∑ k : Coordinate 2, fderiv ℝ
    (fun z => fderiv ℝ g z (coordinateVector k)) (pairCoordinates q) (coordinateVector k)
  simp_rw [second_directional_fderiv_evaluation_at _ _ _ hg]
  exact pair_coordinates_bilinear_trace (fderiv ℝ (fun z => fderiv ℝ g z) (pairCoordinates q))

#print axioms pair_coordinates_bilinear_trace
#print axioms pair_coordinates_weighted_laplacian
end TheoremT.Continuum
