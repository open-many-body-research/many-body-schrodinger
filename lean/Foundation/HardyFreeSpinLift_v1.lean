import HardyFreeGraph_v2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! Norm-preserving finite spin lift of an actual scalar positive free inverse. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

def scalarSpinLiftLinear {N : ℕ} (R : SpatialL2 N →L[ℂ] SpatialL2 N) :
    SpinSpace N →ₗ[ℂ] SpinSpace N where
  toFun ψ := WithLp.toLp 2 (fun σ => R (ψ σ))
  map_add' ψ φ := by
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact map_add R _ _
  map_smul' c ψ := by
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact map_smul R c _

theorem scalarSpinLiftLinear_norm_le {N : ℕ} (R : SpatialL2 N →L[ℂ] SpatialL2 N)
    (ψ : SpinSpace N) : ‖scalarSpinLiftLinear R ψ‖ ≤ ‖R‖ * ‖ψ‖ := by
  have hs : ‖scalarSpinLiftLinear R ψ‖^2 ≤ ‖R‖^2 * ‖ψ‖^2 := by
    calc
      ‖scalarSpinLiftLinear R ψ‖^2 = ∑ σ : SpinConfiguration N, ‖R (ψ σ)‖^2 :=
        PiLp.norm_sq_eq_of_L2 _ _
      _ ≤ ∑ σ : SpinConfiguration N, (‖R‖*‖ψ σ‖)^2 :=
        Finset.sum_le_sum (fun σ _ => pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm _) 2)
      _ = ‖R‖^2 * ‖ψ‖^2 := by
        simp_rw [mul_pow]
        rw [←Finset.mul_sum,←PiLp.norm_sq_eq_of_L2]
  exact le_of_sq_le_sq (by simpa only [mul_pow] using hs)
    (mul_nonneg (norm_nonneg R) (norm_nonneg ψ))

def scalarSpinLift {N : ℕ} (R : SpatialL2 N →L[ℂ] SpatialL2 N) :
    SpinSpace N →L[ℂ] SpinSpace N :=
  (scalarSpinLiftLinear R).mkContinuous ‖R‖ (scalarSpinLiftLinear_norm_le R)

@[simp] theorem scalarSpinLift_apply {N : ℕ} (R : SpatialL2 N →L[ℂ] SpatialL2 N)
    (ψ : SpinSpace N) (σ : SpinConfiguration N) : scalarSpinLift R ψ σ = R (ψ σ) := rfl

theorem scalarSpinLift_norm_le {N : ℕ} (R : SpatialL2 N →L[ℂ] SpatialL2 N) :
    ‖scalarSpinLift R‖ ≤ ‖R‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R) (scalarSpinLiftLinear_norm_le R)

theorem scalarSpinLift_fermionic {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (R : SpatialL2 N →L[ℂ] SpatialL2 N) (hR : ∀ f, positiveFreeGraph μ (R f) f)
    {ψ : SpinSpace N} (hψ : ψ ∈ fermionicSubspace N) :
    scalarSpinLift R ψ ∈ fermionicSubspace N :=
  positiveFreeGraph_solutions_fermionic hμ hψ (fun σ => hR (ψ σ))

def fermionicFreeLift {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (R : SpatialL2 N →L[ℂ] SpatialL2 N) (hR : ∀ f, positiveFreeGraph μ (R f) f) :
    FermionicSpace N →L[ℂ] FermionicSpace N :=
  (scalarSpinLift R).restrict (fun _ hψ => scalarSpinLift_fermionic hμ R hR hψ)

@[simp] theorem fermionicFreeLift_apply {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (R : SpatialL2 N →L[ℂ] SpatialL2 N) (hR : ∀ f, positiveFreeGraph μ (R f) f)
    (ψ : FermionicSpace N) (σ : SpinConfiguration N) :
    (fermionicFreeLift hμ R hR ψ).val σ = R (ψ.val σ) := rfl

theorem fermionicFreeLift_solve {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (R : SpatialL2 N →L[ℂ] SpatialL2 N) (hR : ∀ f, positiveFreeGraph μ (R f) f)
    (ψ : FermionicSpace N) (σ : SpinConfiguration N) :
    positiveFreeGraph μ ((fermionicFreeLift hμ R hR ψ).val σ) (ψ.val σ) := hR _

theorem fermionicFreeLift_hasH2 {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (R : SpatialL2 N →L[ℂ] SpatialL2 N) (hR : ∀ f, positiveFreeGraph μ (R f) f)
    (ψ : FermionicSpace N) : (fermionicFreeLift hμ R hR ψ).val ∈ targetDomain N :=
  ⟨(fermionicFreeLift hμ R hR ψ).property,
    fun σ => positiveFreeGraph_hasH2 (fermionicFreeLift_solve hμ R hR ψ σ)⟩

theorem fermionicFreeLift_norm_le {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (R : SpatialL2 N →L[ℂ] SpatialL2 N) (hR : ∀ f, positiveFreeGraph μ (R f) f) :
    ‖fermionicFreeLift hμ R hR‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro ψ
  exact scalarSpinLiftLinear_norm_le R ψ.val

#print axioms scalarSpinLift_norm_le
#print axioms fermionicFreeLift_hasH2
#print axioms fermionicFreeLift_norm_le
end TheoremT.Continuum
