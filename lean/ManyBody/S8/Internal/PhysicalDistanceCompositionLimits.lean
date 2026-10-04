import ManyBody.S8.Internal.PhysicalDistanceCompositionGeometry
import ConfigurationLpDominated_v1
import WeakH2JetClosure_v1
import HardyDilationCore_v1
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic
/-! Actual smooth regularization of the literal physical three-distance map.
The regularized values converge everywhere, and their genuine first/second
Frechet jets converge at every actual collision-free configuration. Uniform
physical inverse-distance bounds give true compact L2 domination, with no
measure transport or assumed derivative/limit bridge.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def regularizedPhysicalDistanceTriple (δ : ℝ) (x : Configuration 2) : Fin 3 → ℝ :=
  fun j => regularizedLinearRadius (physicalDistanceLinearMaps j) δ x

def regularizedPhysicalDistanceGradient (δ : ℝ) (x v : Configuration 2) : Fin 3 → ℝ :=
  fun j => fderiv ℝ (regularizedLinearRadius (physicalDistanceLinearMaps j) δ) x v

def regularizedPhysicalDistanceHessian (δ : ℝ) (x v w : Configuration 2) : Fin 3 → ℝ :=
  fun j => fderiv ℝ
    (fun y => fderiv ℝ (regularizedLinearRadius (physicalDistanceLinearMaps j) δ) y v) x w

theorem regularized_physical_distance_contDiff {δ : ℝ} (hδ : 0<δ) :
    ContDiff ℝ ∞ (regularizedPhysicalDistanceTriple δ) :=
  contDiff_pi.mpr fun j => regularizedLinearRadius_contDiff (physicalDistanceLinearMaps j) hδ

theorem regularized_physical_distance_fderiv {δ : ℝ} (hδ : 0<δ)
    (x v : Configuration 2) :
    fderiv ℝ (regularizedPhysicalDistanceTriple δ) x v=
      regularizedPhysicalDistanceGradient δ x v := by
  change fderiv ℝ (fun x j => regularizedLinearRadius (physicalDistanceLinearMaps j) δ x) x v=_
  rw [fderiv_pi (fun j => (regularizedLinearRadius_contDiff
    (physicalDistanceLinearMaps j) hδ).differentiable (by simp) x)]
  rfl

theorem regularized_physical_distance_mixed_fderiv {δ : ℝ} (hδ : 0<δ)
    (x v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (regularizedPhysicalDistanceTriple δ) y v) x w=
      regularizedPhysicalDistanceHessian δ x v w := by
  have he : (fun y => fderiv ℝ (regularizedPhysicalDistanceTriple δ) y v)=
      (fun y => regularizedPhysicalDistanceGradient δ y v) :=
    funext fun y => regularized_physical_distance_fderiv hδ y v
  rw [he]
  change fderiv ℝ (fun y j => fderiv ℝ (regularizedLinearRadius (physicalDistanceLinearMaps j) δ) y v) x w=_
  rw [fderiv_pi (fun j =>
    (((regularizedLinearRadius_contDiff (physicalDistanceLinearMaps j) hδ).fderiv_right
      (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const).differentiable (by simp) x)]
  rfl

theorem regularized_physical_distance_gradient_norm_le {δ : ℝ} (hδ : 0<δ)
    (x v : Configuration 2) :
    ‖regularizedPhysicalDistanceGradient δ x v‖≤2*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  exact (regularizedLinearRadius_partial_abs_bound (physicalDistanceLinearMaps j) hδ x v).trans
    (physical_distance_map_norm_le j v)

theorem regularized_physical_distance_hessian_norm_le {δ : ℝ} (hδ : 0<δ)
    {x : Configuration 2} (hx : collisionFree x) (v w : Configuration 2) :
    ‖regularizedPhysicalDistanceHessian δ x v w‖≤
      8*‖v‖*‖w‖*physicalInverseDistanceBudget x := by
  have hb : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun j _ => by positivity
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hi : ‖physicalDistanceLinearMaps j x‖⁻¹≤physicalInverseDistanceBudget x :=
    (show ‖physicalDistanceLinearMaps j x‖⁻¹≤∑ k:Fin 3, ‖physicalDistanceLinearMaps k x‖⁻¹ from
      Finset.single_le_sum (f:=fun k:Fin 3 => ‖physicalDistanceLinearMaps k x‖⁻¹)
        (fun k _ => inv_nonneg.mpr (norm_nonneg _)) (Finset.mem_univ j))
  have hc := regularizedLinearRadius_mixed_coulomb_bound (physicalDistanceLinearMaps j) hδ
    (physical_distance_maps_nonzero hx j) v w
  have hprod : 2*‖physicalDistanceLinearMaps j v‖*‖physicalDistanceLinearMaps j w‖≤
      8*‖v‖*‖w‖ := by
    have hh := mul_le_mul (physical_distance_map_norm_le j v)
      (physical_distance_map_norm_le j w) (norm_nonneg _) (by positivity)
    nlinarith
  exact hc.trans ((div_le_div_of_nonneg_right hprod (norm_nonneg _)).trans
    (by simpa only [div_eq_mul_inv] using (mul_le_mul_of_nonneg_left hi (by positivity : 0≤8*‖v‖*‖w‖))))

theorem regularized_physical_distance_tendsto
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (x : Configuration 2) :
    Tendsto (fun n => regularizedPhysicalDistanceTriple (δ n) x) atTop
      (𝓝 (physicalDistanceTriple x)) :=
  tendsto_pi_nhds.mpr fun j => regularizedLinearRadius_tendsto (physicalDistanceLinearMaps j) hδ x

theorem regularized_physical_distance_gradient_tendsto
    {δ : ℕ → ℝ} (hp : ∀ n, 0<δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration 2} (hx : collisionFree x) (v : Configuration 2) :
    Tendsto (fun n => regularizedPhysicalDistanceGradient (δ n) x v) atTop
      (𝓝 (physicalDistanceGradient x v)) :=
  tendsto_pi_nhds.mpr fun j => regularizedLinearRadius_partial_tendsto (physicalDistanceLinearMaps j)
    hp hδ (physical_distance_maps_nonzero hx j) v

theorem regularized_physical_distance_hessian_tendsto
    {δ : ℕ → ℝ} (hp : ∀ n, 0<δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration 2} (hx : collisionFree x) (v w : Configuration 2) :
    Tendsto (fun n => regularizedPhysicalDistanceHessian (δ n) x v w) atTop
      (𝓝 (physicalDistanceHessian x v w)) :=
  tendsto_pi_nhds.mpr fun j => regularizedLinearRadius_hessian_tendsto (physicalDistanceLinearMaps j)
    hp hδ (physical_distance_maps_nonzero hx j) v w

#print axioms regularized_physical_distance_mixed_fderiv
#print axioms regularized_physical_distance_hessian_norm_le
#print axioms regularized_physical_distance_hessian_tendsto
end ManyBody.S8