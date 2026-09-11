import ScalarCoulombForm_v1
import CoulombH1Quadratic_v1

/-! Assembly of actual scalar component form values into the fermionic spin form. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem scalarCoulombH1FormValue_smul {N : ℕ} {Z : ℝ} {f : SpatialL2 N} {q : ℝ}
    (c : ℂ) (hq : scalarCoulombH1FormValue N Z f q) :
    scalarCoulombH1FormValue N Z (c • f) (‖c‖^2 * q) := by
  obtain ⟨d,hd,he⟩ := scalarCoulombH1FormValue_iff_integral.mp hq
  apply scalarCoulombH1FormValue_iff_integral.mpr
  refine ⟨fun k => c • d k,fun k => weakPartial_smul c (hd k),?_⟩
  have hp : (∫ x, coulombPotential N Z x * ‖(c • f : SpatialL2 N) x‖^2) =
      ‖c‖^2 * ∫ x, coulombPotential N Z x * ‖f x‖^2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply] at hx
    rw [hx,norm_smul,mul_pow]
    ring
  simp only [norm_smul,mul_pow,← Finset.mul_sum]
  rw [hp,he]
  ring

theorem coulombH1FormValue_of_scalar_components {N : ℕ} {Z : ℝ} (ψ : SpinSpace N)
    (hψ : ψ ∈ fermionicSubspace N) (q : SpinConfiguration N → ℝ)
    (hq : ∀ σ, scalarCoulombH1FormValue N Z (ψ σ) (q σ)) :
    coulombH1FormValue N Z ψ (∑ σ, q σ) := by
  choose d v hd hv he using hq
  refine ⟨hψ,fun k => WithLp.toLp 2 (fun σ => d σ k),WithLp.toLp 2 v,hd,hv,?_⟩
  unfold coulombH1Energy
  rw [← rayleighNumerator_eq_real_inner]
  simp only [PiLp.norm_sq_eq_of_L2,rayleighNumerator]
  simp_rw [he,scalarCoulombH1Energy]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [Finset.sum_comm]

#print axioms scalarCoulombH1FormValue_smul
#print axioms coulombH1FormValue_of_scalar_components
end TheoremT.Continuum
