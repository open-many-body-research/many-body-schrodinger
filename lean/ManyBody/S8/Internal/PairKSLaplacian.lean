import TwoElectronRelativeSobolev_v1
import SecondDirectionalLinearAt_v1

/-! The original physical Laplacian is covariant under the exact orthogonal Hadamard map. The proof expands genuine second directional derivatives and cancels mixed bilinear terms; it supplies no Hamiltonian graph or collision premise. -/

noncomputable section
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem relative_bilinear_trace
    (B : Configuration 2 →L[ℝ] Configuration 2 →L[ℝ] ℂ) :
    (∑ k : Coordinate 2, B (twoElectronRelativeEquiv (coordinateVector k))
      (twoElectronRelativeEquiv (coordinateVector k))) =
      ∑ k : Coordinate 2, B (coordinateVector k) (coordinateVector k) := by
  simp only [Coordinate,Fintype.sum_prod_type,Fin.sum_univ_two]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [twoElectronRelative_basis,twoElectronRelative_basis]
  simp only [map_smul,map_add,add_apply,smul_apply,
    Complex.real_smul,Complex.ofReal_inv]
  norm_num [twoElectronRelativeSign]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast hs
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hn]
  rw [hc]
  ring

theorem relative_smoothLaplacian {g : Configuration 2 → ℂ} (x : Configuration 2)
    (hg : ContDiffAt ℝ 2 g (twoElectronRelativeEquiv x)) :
    smoothLaplacian (g ∘ twoElectronRelativeEquiv) x =
      smoothLaplacian g (twoElectronRelativeEquiv x) := by
  have hd (v : Configuration 2) :
      fderiv ℝ (fun z => fderiv ℝ (g ∘ twoElectronRelativeEquiv) z v) x v =
      fderiv ℝ (fun z => fderiv ℝ g z (twoElectronRelativeEquiv v))
        (twoElectronRelativeEquiv x) (twoElectronRelativeEquiv v) :=
    second_directional_linear_at twoElectronRelativeEquiv.toContinuousLinearEquiv.toContinuousLinearMap
      x v v hg
  change (∑ k : Coordinate 2, fderiv ℝ (fun z => fderiv ℝ
    (g ∘ twoElectronRelativeEquiv) z (coordinateVector k)) x (coordinateVector k)) =
    ∑ k : Coordinate 2, fderiv ℝ (fun z => fderiv ℝ g z (coordinateVector k))
      (twoElectronRelativeEquiv x) (coordinateVector k)
  simp_rw [hd]
  simp_rw [second_directional_fderiv_evaluation_at _ _ _ hg]
  exact relative_bilinear_trace _

#print axioms relative_smoothLaplacian
end ManyBody.S8