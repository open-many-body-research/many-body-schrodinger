import ManyBody.S8.Internal.NormalizedPhysicalH2Approximation
import HardyFermionicH1Projection_v1
import Mathlib.Tactic
/-! Finite sums of genuine physical weak H2 errors.
The original distributional derivative rules give actual first and every
ordered second weak family of one literal finite sum. Actual L2 representatives
sum almost everywhere, and derived component bounds give the true43-component
H2 norm. Physical consumers supply the already-proved local chart errors. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_finite_sum_norm_bound {n : ℕ} {G : Fin n → SpatialL2 2}
    {C : Fin n → ℝ} {τ : ℝ} (hG : ∀i,‖G i‖≤τ*C i) :
    ‖∑i,G i‖≤τ*(∑i,C i) := by
  calc
    _≤∑i,‖G i‖ := norm_sum_le _ _
    _≤∑i,τ*C i := Finset.sum_le_sum (fun i _ => hG i)
    _=τ*(∑i,C i) := (Finset.mul_sum _ _ _).symm

theorem physical_finite_weakH2_error_sum {n : ℕ}
    (F : Fin n → SpatialL2 2) (d : Fin n → Coordinate 2 → SpatialL2 2)
    (e : Fin n → Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (f : Fin n → Configuration 2 → ℂ) {C : Fin n → ℝ} {τ : ℝ}
    (hτ : 0≤τ) (hC : ∀i,0≤C i)
    (hAE : ∀i,(F i : Configuration 2 → ℂ)=ᵐ[volume]f i)
    (hd : ∀i k,WeakPartial (F i) (d i k) k)
    (he : ∀i k l,WeakPartial (d i k) (e i k l) l)
    (h0 : ∀i,‖F i‖≤τ*C i) (h1 : ∀i k,‖d i k‖≤τ*C i)
    (h2 : ∀i k l,‖e i k l‖≤τ*C i) :
    (∑i,F i : SpatialL2 2)=ᵐ[volume](fun x => ∑i,f i x) ∧
    (∀k,WeakPartial (∑i,F i) (∑i,d i k) k) ∧
    (∀k l,WeakPartial (∑i,d i k) (∑i,e i k l) l) ∧
    HasH2 (∑i,F i) ∧
    ‖∑i,F i‖≤τ*(∑i,C i) ∧
    (∀k,‖∑i,d i k‖≤τ*(∑i,C i)) ∧
    (∀k l,‖∑i,e i k l‖≤τ*(∑i,C i)) ∧
    physicalH2ComponentNorm (∑i,F i) (fun k => ∑i,d i k)
      (fun k l => ∑i,e i k l)≤7*τ*(∑i,C i) := by
  have hA : ∀ᵐx∂volume,∀i,(F i : Configuration 2 → ℂ) x=f i x := eventually_all.mpr hAE
  have hsumAE := Lp.coeFn_fun_finsetSum Finset.univ F
  have hfirst (k : Coordinate 2) : WeakPartial (∑i,F i) (∑i,d i k) k :=
    weakPartial_finsetSum Finset.univ F (fun i => d i k) k (fun i _ => hd i k)
  have hsecond (k l : Coordinate 2) : WeakPartial (∑i,d i k) (∑i,e i k l) l :=
    weakPartial_finsetSum Finset.univ (fun i => d i k) (fun i => e i k l) l (fun i _ => he i k l)
  have hbound0 := physical_finite_sum_norm_bound h0
  have hbound1 (k : Coordinate 2) := physical_finite_sum_norm_bound (fun i => h1 i k)
  have hbound2 (k l : Coordinate 2) := physical_finite_sum_norm_bound (fun i => h2 i k l)
  refine ⟨?_,hfirst,hsecond,⟨(fun k => ∑i,d i k),hfirst,fun k l => ⟨∑i,e i k l,hsecond k l⟩⟩,
    hbound0,hbound1,hbound2,?_⟩
  · filter_upwards [hsumAE,hA] with x hx hy
    rw [hx]
    exact Finset.sum_congr rfl (fun i _ => hy i)
  · simpa only [mul_assoc] using physicalH2ComponentNorm_le_common
      (∑i,F i) (fun k => ∑i,d i k) (fun k l => ∑i,e i k l)
      (τ*(∑i,C i)) (mul_nonneg hτ (Finset.sum_nonneg (fun i _ => hC i))) hbound0 hbound1 hbound2

#print axioms physical_finite_sum_norm_bound
#print axioms physical_finite_weakH2_error_sum
end ManyBody.S8