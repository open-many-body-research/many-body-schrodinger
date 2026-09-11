import CompactDefectKernel_v1
import SpectralBottom_v2
import Mathlib.Analysis.SpecificLimits.Basic

/-! Spectral points below a coercive rank-one comparison are actual
eigenvalues. This proves the attainment step, without a spectral measure,
compact resolvent or an assumed eigenfunction. The comparison itself stays
explicit and must be proved for any physical application. -/
noncomputable section
open Filter
open scoped Topology LinearPMap
namespace TheoremT.OperatorTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem selfAdjoint_spectral_eigenvector_of_scalar_defect
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (l : E →L[ℂ] ℂ)
    (β C : ℝ) (hC : 0 ≤ C)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖^2 ≤
      (inner ℂ (x : E) (A x)).re + C * ‖l (x : E)‖^2)
    (r : ℝ) (hr : (r : ℂ) ∈ unboundedSpectrum A) (hrβ : r < β) :
    ∃ u : A.domain, ‖(u : E)‖ = 1 ∧ A u = (r : ℂ) • (u : E) := by
  have hex : ∀ n : ℕ, ∃ x : A.domain, ‖(x : E)‖ = 1 ∧
      ‖A x - (r : ℂ) • (x : E)‖ < 1 / ((n : ℝ)+1) := by
    intro n
    apply selfAdjoint_spectral_point_approximate_eigenvector A hA r hr
    positivity
  choose x hx hres using hex
  let S := operatorShift A (r : ℂ)
  have hsform : ∀ v : S.domain, (β-r) * ‖(v : E)‖^2 ≤
      (inner ℂ (v : E) (S v)).re + C * ‖l (v : E)‖^2 := by
    intro v
    have hs : (inner ℂ (v : E) (S v)).re =
        (inner ℂ (v : E) (A v)).re - r * ‖(v : E)‖^2 := by
      change (inner ℂ (v : E) (A v - (r : ℂ) • (v : E))).re = _
      rw [inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    rw [hs]
    have hv := hform v
    linarith
  have hres0 : Tendsto (fun n => ‖S (x n)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (hres n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨u,hu,hSu⟩ := closed_operator_kernel_of_scalar_defect S
    (operatorShift_isClosed A hA.isClosed (r : ℂ)) l (sub_pos.mpr hrβ) hC hsform x hx hres0
  refine ⟨u,hu,?_⟩
  exact sub_eq_zero.mp hSu

#print axioms selfAdjoint_spectral_eigenvector_of_scalar_defect
end TheoremT.OperatorTheory
