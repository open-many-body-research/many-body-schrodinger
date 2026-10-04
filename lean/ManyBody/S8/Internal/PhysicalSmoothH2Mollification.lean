import ManyBody.S8.CoulombNormalizedCompactApproximation
import HardySobolevDensity_v1
import MollifierUniformSupport_v1

/-! One physical mollifier index approximates every genuine weak H2 component.
All derivatives and compact support refer to the original physical space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_H2_mollification_components_eventually (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop, ‖mollifyLp m f-f‖<δ ∧
      (∀ k, ‖mollifyLp m (d k)-d k‖<δ) ∧
      (∀ k l, ‖mollifyLp m (e k l)-e k l‖<δ) := by
  have h0 : ∀ᶠ m : ℕ in atTop, ‖mollifyLp m f-f‖<δ := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.1 (mollifyLp_tendsto f) δ hδ)
  have h1 : ∀ᶠ m : ℕ in atTop, ∀ k, ‖mollifyLp m (d k)-d k‖<δ := by
    apply eventually_all.mpr
    intro k
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.1 (mollifyLp_tendsto (d k)) δ hδ)
  have h2 : ∀ᶠ m : ℕ in atTop, ∀ k l, ‖mollifyLp m (e k l)-e k l‖<δ := by
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro l
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.1 (mollifyLp_tendsto (e k l)) δ hδ)
  exact h0.and (h1.and h2)

def PhysicalSmoothMollificationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (S : ℝ) (m : ℕ) : Prop :=
  let u := mollify (mollifierKernel 2 m) f
  let g := mollifyLp m f
  let dg := fun k => mollifyLp m (d k)
  let eg := fun k l => mollifyLp m (e k l)
  ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u⊆closedBall 0 (S+2) ∧
  (g : Configuration 2 → ℂ) =ᵐ[volume] u ∧
  (∀ k, (dg k : Configuration 2 → ℂ) =ᵐ[volume] smoothPartial u k) ∧
  (∀ k l, (eg k l : Configuration 2 → ℂ) =ᵐ[volume] smoothPartial (smoothPartial u k) l) ∧
  (∀ k, WeakPartial g (dg k) k) ∧ (∀ k l, WeakPartial (dg k) (eg k l) l)

theorem physical_smooth_mollification_data (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {S : ℝ} (hs : ∀ᵐ y ∂volume, S<‖y‖ → f y=0) (m : ℕ) :
    PhysicalSmoothMollificationData f d e S m := by
  have hsupp := mollify_tsupport_subset_closedBall hs m
  have hc : HasCompactSupport (mollify (mollifierKernel 2 m) f) :=
    (isCompact_closedBall (0 : Configuration 2) (S+2)).of_isClosed_subset
      (isClosed_tsupport _) hsupp
  exact ⟨mollify_contDiff _ (mollifierKernel_contDiff 2 m)
    (mollifierKernel_hasCompactSupport 2 m) f,hc,hsupp,mollifyLp_ae m f,
    (fun k => mollifyLp_partial_ae (hd k) m),
    (fun k l => mollifyLp_second_ae (hd k) (he k l) m),
    (fun k => mollifyLp_weakPartial (hd k) m),
    (fun k l => mollifyLp_weakPartial (he k l) m)⟩

theorem physicalCompactState_ae_support (f : SpatialL2 2) (R : ℝ) (hR : 0<R) :
    ∀ᵐ x ∂volume, 2*R<‖x‖ → physicalCompactState R hR f x=0 := by
  filter_upwards [physicalCompactState_ae R hR f] with x hx
  intro hnorm
  rw [hx,physicalCompactCutoff_eq_zero hR (by linarith),zero_smul]

theorem physical_smoothPartial_const_smul (c : ℂ) {u : Configuration 2 → ℂ}
    (hu : ContDiff ℝ ∞ u) (k : Coordinate 2) :
    smoothPartial (fun x => c • u x) k=fun x => c • smoothPartial u k x := by
  funext x
  dsimp only [smoothPartial]
  rw [fderiv_fun_const_smul (hu.differentiable (by simp) x) c,smul_apply]

theorem physical_smoothSecond_const_smul (c : ℂ) {u : Configuration 2 → ℂ}
    (hu : ContDiff ℝ ∞ u) (k l : Coordinate 2) :
    smoothPartial (smoothPartial (fun x => c • u x) k) l=
      fun x => c • smoothPartial (smoothPartial u k) l x := by
  rw [physical_smoothPartial_const_smul c hu k,
    physical_smoothPartial_const_smul c (smoothPartial_contDiff hu k) l]

theorem scalar_eigen_H2_graph_residual_le {Z E : ℝ} {f g h : SpatialL2 2}
    (hf : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (hg : scalarHamiltonianGraph 2 Z g h)
    (d dg : Coordinate 2 → SpatialL2 2)
    (e eg : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hdg : ∀ k, WeakPartial g (dg k) k) (heg : ∀ k l, WeakPartial (dg k) (eg k l) l) :
    ‖h-(E:ℂ) • g‖≤(3+2*(2*|Z|+1)+|E|)*
      physicalH2ComponentNorm (g-f) (fun k => dg k-d k) (fun k l => eg k l-e k l) := by
  have hsub : scalarHamiltonianGraph 2 Z (g-f) (h-(E:ℂ) • f) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using scalar_graph_add hg (scalar_graph_smul (-1:ℂ) hf)
  have hb := scalar_graph_norm_le_physicalH2 Z hsub (fun k => dg k-d k)
    (fun k l => eg k l-e k l) (fun k => weakPartial_sub_h1 (hdg k) (hd k))
    (fun k l => weakPartial_sub_h1 (heg k l) (he k l))
  have h0 := (physicalH2ComponentNorm_bounds (g-f) (fun k => dg k-d k)
    (fun k l => eg k l-e k l)).1
  have hid : h-(E:ℂ) • g=(h-(E:ℂ) • f)-(E:ℂ) • (g-f) := by
    rw [smul_sub]; abel
  rw [hid]
  have hn : ‖(E:ℂ)‖=|E| := by simp [Real.norm_eq_abs]
  have hs := norm_sub_le (h-(E:ℂ) • f) ((E:ℂ) • (g-f))
  rw [norm_smul,hn] at hs
  have hm := mul_le_mul_of_nonneg_left h0 (abs_nonneg E)
  nlinarith

#print axioms physical_H2_mollification_components_eventually
#print axioms physical_smooth_mollification_data
#print axioms physical_smoothSecond_const_smul
#print axioms scalar_eigen_H2_graph_residual_le
end ManyBody.S8