import SpectatorInsertion_v1
import SecondDirectionalLinearAt_v1
import HardyLaplacianCore_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem configuration_split_laplacian {N : ℕ} (i : Fin N)
    {f : Configuration N → ℂ} (q : Position × SpectatorConfiguration i)
    (hf : ContDiffAt ℝ 2 f ((configurationProductEquiv i).symm q)) :
    (∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ
      (f ∘ (configurationProductEquiv i).symm) z (ksTargetBasis k,0)) q (ksTargetBasis k,0)) +
    (∑ k : SpectatorCoordinate i, fderiv ℝ (fun z => fderiv ℝ
      (f ∘ (configurationProductEquiv i).symm) z (0,spectatorBasis k)) q (0,spectatorBasis k)) =
      smoothLaplacian f ((configurationProductEquiv i).symm q) := by
  have he (k : Fin 3) : (configurationProductEquiv i).symm (ksTargetBasis k,0)=coordinateVector (i,k) :=
    electronInsertion_ksTargetBasis i k
  have hs (k : SpectatorCoordinate i) :
      (configurationProductEquiv i).symm (0,spectatorBasis k)=coordinateVector k.val := spectatorInsertion_basis i k
  have hd (v : Position × SpectatorConfiguration i) :
      fderiv ℝ (fun z => fderiv ℝ (f ∘ (configurationProductEquiv i).symm) z v) q v =
      fderiv ℝ (fun z => fderiv ℝ f z ((configurationProductEquiv i).symm v))
        ((configurationProductEquiv i).symm q) ((configurationProductEquiv i).symm v) :=
    second_directional_linear_at (configurationProductEquiv i).symm.toContinuousLinearMap q v v hf
  simp_rw [hd,he,hs]
  exact (sum_coordinates_split i (fun k => smoothPartial (smoothPartial f k) k
    ((configurationProductEquiv i).symm q))).symm

#print axioms configuration_split_laplacian
end TheoremT.Continuum
