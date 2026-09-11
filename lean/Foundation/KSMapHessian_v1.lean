import KSMapDerivative_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem ksJacobian_bilinear_symmetry (y v : KSSpace) (i : Fin 3) :
    (∑ k : Fin 4, ksJacobian y i k*v k) = ∑ k : Fin 4, ksJacobian v i k*y k := by
  fin_cases i <;> simp [ksJacobian,Fin.sum_univ_succ] <;> ring

theorem ksMap_coordinate_second_fderiv (y v w : KSSpace) (i : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => ksMap z i) x v) y w =
      ∑ k : Fin 4, ksJacobian v i k*w k := by
  let L : KSSpace →L[ℝ] ℝ := ∑ k : Fin 4, ksJacobian v i k • EuclideanSpace.proj k
  have he : (fun x => fderiv ℝ (fun z => ksMap z i) x v)=(L : KSSpace → ℝ) := by
    funext x
    rw [ksMap_coordinate_fderiv,ksJacobian_bilinear_symmetry]
    simp [L,ContinuousLinearMap.sum_apply]
  rw [he,L.fderiv]
  simp [L,ContinuousLinearMap.sum_apply]

def ksBasis (k : Fin 4) : KSSpace := WithLp.toLp 2 (Pi.single k 1)

theorem ksMap_coordinate_laplacian_zero (y : KSSpace) (i : Fin 3) :
    (∑ k : Fin 4, fderiv ℝ (fun x => fderiv ℝ (fun z => ksMap z i) x (ksBasis k)) y (ksBasis k))=0 := by
  simp_rw [ksMap_coordinate_second_fderiv]
  fin_cases i <;> norm_num [ksJacobian,ksBasis,Fin.sum_univ_succ,Pi.single_apply]

theorem ksMap_fderiv_coordinate (y v : KSSpace) (i : Fin 3) :
    (fderiv ℝ ksMap y v) i = ∑ k : Fin 4, ksJacobian y i k*v k := by
  have hd := (ksMap_contDiff.differentiable (by simp)) y
  have hh := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (ksMap y) i).comp y hd.hasFDerivAt
  change HasFDerivAt (fun x => ksMap x i) _ y at hh
  have he := congrArg (fun L : KSSpace →L[ℝ] ℝ => L v) hh.fderiv
  change fderiv ℝ (fun x => ksMap x i) y v=(fderiv ℝ ksMap y v) i at he
  rw [← he,ksMap_coordinate_fderiv]

#print axioms ksMap_coordinate_second_fderiv
#print axioms ksMap_coordinate_laplacian_zero
#print axioms ksMap_fderiv_coordinate
end TheoremT.Continuum
