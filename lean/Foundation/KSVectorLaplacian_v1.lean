import KSMapHessian_v1

noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem ksMap_second_fderiv_coordinate (y v w : KSSpace) (i : Fin 3) :
    (fderiv ℝ (fun x => fderiv ℝ ksMap x v) y w) i =
      fderiv ℝ (fun x => fderiv ℝ (fun z => ksMap z i) x v) y w := by
  have hd : Differentiable ℝ (fun x => fderiv ℝ ksMap x v) :=
    ((ksMap_contDiff.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hh := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (fderiv ℝ ksMap y v) i).comp y (hd y).hasFDerivAt
  change HasFDerivAt (fun x => (fderiv ℝ ksMap x v) i) _ y at hh
  have he := congrArg (fun L : KSSpace →L[ℝ] ℝ => L w) hh.fderiv
  change fderiv ℝ (fun x => (fderiv ℝ ksMap x v) i) y w =
    (fderiv ℝ (fun x => fderiv ℝ ksMap x v) y w) i at he
  rw [← he]
  congr 2
  funext x
  rw [ksMap_fderiv_coordinate,ksMap_coordinate_fderiv]

theorem ksMap_vector_laplacian_zero (y : KSSpace) :
    (∑ k : Fin 4, fderiv ℝ (fun x => fderiv ℝ ksMap x (ksBasis k)) y (ksBasis k))=0 := by
  ext i
  change (EuclideanSpace.proj i) (∑ k : Fin 4, fderiv ℝ (fun x => fderiv ℝ ksMap x (ksBasis k)) y (ksBasis k)) = 0
  rw [map_sum]
  change (∑ k : Fin 4, (fderiv ℝ (fun x => fderiv ℝ ksMap x (ksBasis k)) y (ksBasis k)) i)=0
  simp only [ksMap_second_fderiv_coordinate]
  exact ksMap_coordinate_laplacian_zero y i

#print axioms ksMap_second_fderiv_coordinate
#print axioms ksMap_vector_laplacian_zero
end TheoremT.Continuum
