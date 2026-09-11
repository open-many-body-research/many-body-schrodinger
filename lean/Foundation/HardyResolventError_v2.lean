import HardyResolventError_v1

/-! Boundedness of the actual full fermionic Coulomb resolvent error. The norm
estimate comes from the exact positive-free energy identity, not an assumed
bounded potential or a finite-dimensional surrogate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

def coulombFreeBoundConstant (N : ℕ) (Z : ℝ) : ℝ :=
  2*(|Z| *(N:ℝ)+(N.choose 2:ℝ))

theorem coulombFreeBoundConstant_nonneg (N : ℕ) (Z : ℝ) :
    0 ≤ coulombFreeBoundConstant N Z := by unfold coulombFreeBoundConstant; positivity

theorem coulombFreeErrorLinear_norm_le (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) :
    ‖coulombFreeErrorLinear N Z μ hμ ψ‖ ≤
      (coulombFreeBoundConstant N Z / Real.sqrt (2*μ)) * ‖ψ‖ := by
  have hs : ∀ σ : SpinConfiguration N,
      positiveFreeGraph μ ((fermionicFreeResolvent N μ hμ ψ).val σ) (ψ.val σ) :=
    fermionicFreeResolvent_solve N hμ ψ
  simp only [positiveFreeGraph] at hs
  choose d e hd he hout using hs
  let ds : Coordinate N → SpinSpace N := fun k => WithLp.toLp 2 (fun σ => d σ k)
  let es : Coordinate N → Coordinate N → SpinSpace N := fun k l => WithLp.toLp 2 (fun σ => e σ k l)
  have hb := coulomb_product_spin_norm_le Z (fermionicFreeResolvent N μ hμ ψ).val ds
    (fun σ k => hd σ k) (coulombFreeErrorLinear N Z μ hμ ψ).val
    (coulombFreeErrorLinear_apply_ae N Z hμ ψ)
  have hg := positiveFreeGraph_spin_gradient_sq_le hμ ds es
    (fun σ k => hd σ k) (fun σ k l => he σ k l) hout
  change ‖coulombFreeErrorLinear N Z μ hμ ψ‖ ≤
    coulombFreeBoundConstant N Z * Real.sqrt (∑ k : Coordinate N, ‖ds k‖^2) at hb
  calc
    ‖coulombFreeErrorLinear N Z μ hμ ψ‖ ≤
        coulombFreeBoundConstant N Z * Real.sqrt (∑ k : Coordinate N, ‖ds k‖^2) := hb
    _ ≤ coulombFreeBoundConstant N Z * Real.sqrt (‖ψ.val‖^2/(2*μ)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (coulombFreeBoundConstant_nonneg N Z)
    _ = (coulombFreeBoundConstant N Z / Real.sqrt (2*μ))*‖ψ‖ := by
      rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_norm]
      change coulombFreeBoundConstant N Z*(‖ψ‖/Real.sqrt (2*μ)) = _
      ring

def coulombFreeError (N : ℕ) (Z μ : ℝ) (hμ : 0 < μ) :
    FermionicSpace N →L[ℂ] FermionicSpace N :=
  (coulombFreeErrorLinear N Z μ hμ).mkContinuous
    (coulombFreeBoundConstant N Z / Real.sqrt (2*μ)) (coulombFreeErrorLinear_norm_le N Z hμ)

theorem norm_coulombFreeError_le (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ‖coulombFreeError N Z μ hμ‖ ≤ coulombFreeBoundConstant N Z / Real.sqrt (2*μ) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (coulombFreeBoundConstant_nonneg N Z) (Real.sqrt_nonneg _))
  exact coulombFreeErrorLinear_norm_le N Z hμ

theorem coulombFreeError_identity (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) :
    (coulombPartialOperator N Z) (fermionicFreeResolventToDomain N Z μ hμ ψ) +
      (μ : ℂ) • fermionicFreeResolvent N μ hμ ψ = ψ + coulombFreeError N Z μ hμ ψ := by
  change _ = ψ + (((coulombPartialOperator N Z) (fermionicFreeResolventToDomain N Z μ hμ ψ) +
    (μ : ℂ) • fermionicFreeResolvent N μ hμ ψ) - ψ)
  abel

#print axioms coulombFreeErrorLinear_norm_le
#print axioms norm_coulombFreeError_le
#print axioms coulombFreeError_identity
end TheoremT.Continuum
