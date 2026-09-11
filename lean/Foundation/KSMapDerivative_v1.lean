import KSMapGeometry_v1
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! Identify the polynomial matrix with the actual Frechet derivatives. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem ksMap_coordinate_fderiv (y v : KSSpace) (i : Fin 3) :
    fderiv ℝ (fun x => ksMap x i) y v =
      ∑ k : Fin 4, ksJacobian y i k*v k := by
  have h (k : Fin 4) := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y k
  fin_cases i
  · change fderiv ℝ (fun x : KSSpace => 2*(x 0*x 2+x 1*x 3)) y v = _
    have hh := (((h 0).mul (h 2)).add ((h 1).mul (h 3))).const_mul 2
    change HasFDerivAt (fun x : KSSpace => 2*(x 0*x 2+x 1*x 3)) _ y at hh
    rw [hh.fderiv]
    simp [ksJacobian,Fin.sum_univ_succ]
    ring
  · change fderiv ℝ (fun x : KSSpace => 2*(x 1*x 2-x 0*x 3)) y v = _
    have hh := (((h 1).mul (h 2)).sub ((h 0).mul (h 3))).const_mul 2
    change HasFDerivAt (fun x : KSSpace => 2*(x 1*x 2-x 0*x 3)) _ y at hh
    rw [hh.fderiv]
    simp [ksJacobian,Fin.sum_univ_succ]
    ring
  · change fderiv ℝ (fun x : KSSpace => x 0^2+x 1^2-x 2^2-x 3^2) y v = _
    have hh := ((((h 0).pow 2).add ((h 1).pow 2)).sub ((h 2).pow 2)).sub ((h 3).pow 2)
    change HasFDerivAt (fun x : KSSpace => x 0^2+x 1^2-x 2^2-x 3^2) _ y at hh
    rw [hh.fderiv]
    simp [ksJacobian,Fin.sum_univ_succ]
    ring

#print axioms ksMap_coordinate_fderiv
end TheoremT.Continuum
