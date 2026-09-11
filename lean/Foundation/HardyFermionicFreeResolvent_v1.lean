import HardyFreeSpinLift_v1
import HardyFreeGraph_v3
import FreeResolvent_v1

/-! The actual Fourier-constructed positive free resolvent lifted to the full
fermionic spin space. Scalar solve, weak H² range and norm hypotheses are discharged. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem freeResolvent_positiveFreeGraph (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialL2 N) : positiveFreeGraph μ (freeResolvent N μ hμ f) f := by
  simpa only [positiveFreeGraph,neg_div] using freeResolvent_solve N hμ f

def fermionicFreeResolvent (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    FermionicSpace N →L[ℂ] FermionicSpace N :=
  fermionicFreeLift hμ (freeResolvent N μ hμ) (freeResolvent_positiveFreeGraph N hμ)

@[simp] theorem fermionicFreeResolvent_apply (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) (σ : SpinConfiguration N) :
    (fermionicFreeResolvent N μ hμ ψ).val σ = freeResolvent N μ hμ (ψ.val σ) := rfl

theorem fermionicFreeResolvent_solve (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) (σ : SpinConfiguration N) :
    positiveFreeGraph μ ((fermionicFreeResolvent N μ hμ ψ).val σ) (ψ.val σ) :=
  freeResolvent_positiveFreeGraph N hμ (ψ.val σ)

theorem fermionicFreeResolvent_hasH2 (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) : (fermionicFreeResolvent N μ hμ ψ).val ∈ targetDomain N :=
  fermionicFreeLift_hasH2 hμ (freeResolvent N μ hμ) (freeResolvent_positiveFreeGraph N hμ) ψ

theorem norm_fermionicFreeResolvent_le (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ‖fermionicFreeResolvent N μ hμ‖ ≤ μ⁻¹ :=
  (fermionicFreeLift_norm_le hμ _ _).trans (norm_freeResolvent_le N hμ)

/-- The free kinetic resolvent on the fermionic Hilbert space. -/
def fermionicFreeKineticResolvent (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    FermionicSpace N →L[ℂ] FermionicSpace N :=
  ContinuousLinearMap.id ℂ (FermionicSpace N) - μ • fermionicFreeResolvent N μ hμ

@[simp] theorem fermionicFreeKineticResolvent_apply (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) (σ : SpinConfiguration N) :
    (fermionicFreeKineticResolvent N μ hμ ψ).val σ =
      freeKineticResolvent N μ hμ (ψ.val σ) := by
  change ψ.val σ - μ • freeResolvent N μ hμ (ψ.val σ) = _
  exact (eq_sub_iff_add_eq.mpr (freeResolvent_partition N hμ (ψ.val σ))).symm

theorem fermionicFreeResolvent_partition (N : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) :
    fermionicFreeKineticResolvent N μ hμ ψ + μ • fermionicFreeResolvent N μ hμ ψ = ψ := by
  change (ψ - μ • fermionicFreeResolvent N μ hμ ψ) + μ • fermionicFreeResolvent N μ hμ ψ = ψ
  exact sub_add_cancel _ _

theorem norm_fermionicFreeKineticResolvent_le (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ‖fermionicFreeKineticResolvent N μ hμ‖ ≤ 1 := by
  have hb : ‖fermionicFreeKineticResolvent N μ hμ‖ ≤ ‖freeKineticResolvent N μ hμ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro ψ
    change ‖(fermionicFreeKineticResolvent N μ hμ ψ).val‖ ≤
      ‖freeKineticResolvent N μ hμ‖ * ‖ψ.val‖
    have he : (fermionicFreeKineticResolvent N μ hμ ψ).val =
        scalarSpinLiftLinear (freeKineticResolvent N μ hμ) ψ.val := by
      apply (WithLp.ext_iff 2).mpr
      funext σ
      exact fermionicFreeKineticResolvent_apply N hμ ψ σ
    rw [he]
    exact scalarSpinLiftLinear_norm_le _ _
  exact hb.trans (norm_freeKineticResolvent_le N hμ)

#print axioms fermionicFreeResolvent_solve
#print axioms fermionicFreeResolvent_hasH2
#print axioms norm_fermionicFreeResolvent_le
#print axioms fermionicFreeResolvent_partition
#print axioms norm_fermionicFreeKineticResolvent_le
end TheoremT.Continuum
