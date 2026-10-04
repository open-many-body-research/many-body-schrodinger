import ManyBody.S8.Internal.PhysicalRadialMollifier
import ManyBody.S8.Internal.PhysicalSmoothH2Mollification
import ManyBody.S8.CoulombNormalizedRadialCompactApproximation

/-! Actual radial convolution transports every genuine physical weak H2
component and preserves configuration isometries and reality. All smooth
representative and compact-support statements refer to the literal kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physicalRadialMollify_covariance (m : ℕ)
    (Q : Configuration 2 ≃ₗᵢ[ℝ] Configuration 2) (f : SpatialL2 2) (x : Configuration 2) :
    mollify (physicalRadialMollifierKernel m) (configurationIsometryPull Q f) x=
      mollify (physicalRadialMollifierKernel m) f (Q x) := by
  unfold mollify
  calc _=(∫ y,physicalRadialMollifierKernel m (x-y) • f (Q y)) := by
         apply integral_congr_ae
         filter_upwards [configurationIsometryPull_ae Q f] with y hy
         simp only [Function.comp_apply] at hy
         rw [hy]
       _=(∫ y,physicalRadialMollifierKernel m (Q x-Q y) • f (Q y)) := by
         congr 1
         funext y
         rw [← map_sub,physicalRadialMollifierKernel_isometry]
       _=(∫ y,physicalRadialMollifierKernel m (Q x-y) • f y) :=
         Q.measurePreserving.integral_comp Q.toHomeomorph.measurableEmbedding
           (fun y : Configuration 2 => physicalRadialMollifierKernel m (Q x-y) • f y)

theorem physicalRadialMollify_isometry (m : ℕ)
    (Q : Configuration 2 ≃ₗᵢ[ℝ] Configuration 2) {f : SpatialL2 2}
    (hf : configurationIsometryPull Q f=f) (x : Configuration 2) :
    mollify (physicalRadialMollifierKernel m) f (Q x)=
      mollify (physicalRadialMollifierKernel m) f x := by
  simpa only [hf] using (physicalRadialMollify_covariance m Q f x).symm

theorem physicalRadialMollifyLp_isometry (m : ℕ)
    (Q : Configuration 2 ≃ₗᵢ[ℝ] Configuration 2) (f : SpatialL2 2) :
    configurationIsometryPull Q (physicalRadialMollifyLp m f)=
      physicalRadialMollifyLp m (configurationIsometryPull Q f) := by
  apply Lp.ext
  have hc := Q.measurePreserving.quasiMeasurePreserving.ae (physicalRadialMollifyLp_ae m f)
  filter_upwards [configurationIsometryPull_ae Q (physicalRadialMollifyLp m f),hc,
    physicalRadialMollifyLp_ae m (configurationIsometryPull Q f)] with x hx hy hz
  simp only [Function.comp_apply] at *
  rw [hx,hy,hz]
  exact (physicalRadialMollify_covariance m Q f x).symm

theorem physicalRadialMollifyLp_permutation (m : ℕ) {f : SpatialL2 2}
    (π : Equiv.Perm (Fin 2)) (hf : pullback π f=f) :
    pullback π (physicalRadialMollifyLp m f)=physicalRadialMollifyLp m f := by
  have h := physicalRadialMollifyLp_isometry m (permuteSpace π) f
  change pullback π (physicalRadialMollifyLp m f)=physicalRadialMollifyLp m (pullback π f) at h
  simpa only [hf] using h

theorem physicalRadialMollifyLp_rotation (m : ℕ) {f : SpatialL2 2}
    (Q : Position ≃ₗᵢ[ℝ] Position) (hf : spatialRotation 2 Q f=f) :
    spatialRotation 2 Q (physicalRadialMollifyLp m f)=physicalRadialMollifyLp m f := by
  simpa only [hf] using physicalRadialMollifyLp_isometry m (configurationRotation 2 Q) f

theorem physicalRadialMollify_real (m : ℕ) {f : SpatialL2 2}
    (hf : ∀ᵐ y ∂volume, (f y).im=0) (x : Configuration 2) :
    (mollify (physicalRadialMollifierKernel m) f x).im=0 := by
  unfold mollify
  by_cases hi : Integrable (fun y => physicalRadialMollifierKernel m (x-y) • f y) volume
  · change Complex.imCLM (∫ y,physicalRadialMollifierKernel m (x-y) • f y)=0
    rw [← Complex.imCLM.integral_comp_comm hi]
    apply integral_eq_zero_of_ae
    filter_upwards [hf] with y hy
    change Complex.imCLM (physicalRadialMollifierKernel m (x-y) • f y)=0
    change Complex.imCLM (f y)=0 at hy
    rw [map_smul,hy,smul_zero]
  · rw [integral_undef hi]
    rfl

theorem physicalRadialMollifyLp_real (m : ℕ) {f : SpatialL2 2}
    (hf : ∀ᵐ y ∂volume, (f y).im=0) :
    ∀ᵐ x ∂volume, (physicalRadialMollifyLp m f x).im=0 := by
  filter_upwards [physicalRadialMollifyLp_ae m f] with x hx
  rw [hx]
  exact physicalRadialMollify_real m hf x

theorem physicalRadialMollifyLp_partial_ae {f g : SpatialL2 2} {k : Coordinate 2}
    (hg : WeakPartial f g k) (m : ℕ) :
    (physicalRadialMollifyLp m g : Configuration 2 → ℂ)=ᵐ[volume]
      smoothPartial (mollify (physicalRadialMollifierKernel m) f) k := by
  rw [smoothPartial_mollify hg _ (physicalRadialMollifierKernel_contDiff m)
    (physicalRadialMollifierKernel_hasCompactSupport m)]
  exact physicalRadialMollifyLp_ae m g

theorem physicalRadialMollifyLp_second_ae {f dk e : SpatialL2 2} {k l : Coordinate 2}
    (hd : WeakPartial f dk k) (he : WeakPartial dk e l) (m : ℕ) :
    (physicalRadialMollifyLp m e : Configuration 2 → ℂ)=ᵐ[volume]
      smoothPartial (smoothPartial (mollify (physicalRadialMollifierKernel m) f) k) l := by
  rw [smoothSecond_mollify hd he _ (physicalRadialMollifierKernel_contDiff m)
    (physicalRadialMollifierKernel_hasCompactSupport m)]
  exact physicalRadialMollifyLp_ae m e

theorem physicalRadialMollifyLp_weakPartial {f g : SpatialL2 2} {k : Coordinate 2}
    (hg : WeakPartial f g k) (m : ℕ) :
    WeakPartial (physicalRadialMollifyLp m f) (physicalRadialMollifyLp m g) k := by
  let u := mollify (physicalRadialMollifierKernel m) f
  have hu : ContDiff ℝ ∞ u := mollify_contDiff _
    (physicalRadialMollifierKernel_contDiff m) (physicalRadialMollifierKernel_hasCompactSupport m) f
  have heq : (fun x => fderiv ℝ u x (coordinateVector k))=
      mollify (physicalRadialMollifierKernel m) g :=
    smoothPartial_mollify hg _ (physicalRadialMollifierKernel_contDiff m)
      (physicalRadialMollifierKernel_hasCompactSupport m)
  have hd : MemLp (fun x => fderiv ℝ u x (coordinateVector k)) 2 volume := by
    rw [heq]
    exact physicalRadialMollify_memLp m g
  have hdeq : hd.toLp (fun x => fderiv ℝ u x (coordinateVector k))=physicalRadialMollifyLp m g := by
    apply Lp.ext
    exact hd.coeFn_toLp.trans ((Filter.EventuallyEq.of_eq heq).trans (physicalRadialMollifyLp_ae m g).symm)
  have hh := classicalDerivative_to_WeakPartial (hu.of_le (by simp)) k
    (physicalRadialMollify_memLp m f) hd
  change WeakPartial (physicalRadialMollifyLp m f) _ k at hh
  rwa [hdeq] at hh

theorem physicalRadialMollifierKernel_eq_zero {m : ℕ} {x : Configuration 2}
    (hx : 2<‖x‖) : physicalRadialMollifierKernel m x=0 := by
  by_contra hn
  have hm := mem_closedBall_zero_iff.mp (physicalRadialMollifierKernel_support m hn)
  linarith [physicalRadialMollifierRadius_le_one m]

theorem physicalRadialMollify_eq_zero_outside {S : ℝ} {f : SpatialL2 2}
    (hs : ∀ᵐ y ∂volume, S<‖y‖ → f y=0) (m : ℕ) {x : Configuration 2}
    (hx : S+2<‖x‖) : mollify (physicalRadialMollifierKernel m) f x=0 := by
  unfold mollify
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with y hy
  by_cases h : S<‖y‖
  · simp only [hy h,smul_zero,Pi.zero_apply]
  · have hb : 2<‖x-y‖ := by
      have he : ‖x‖≤‖x-y‖+‖y‖ := by simpa using norm_add_le (x-y) y
      push Not at h
      linarith
    simp only [physicalRadialMollifierKernel_eq_zero hb,zero_smul,Pi.zero_apply]

theorem physicalRadialMollify_tsupport {S : ℝ} {f : SpatialL2 2}
    (hs : ∀ᵐ y ∂volume, S<‖y‖ → f y=0) (m : ℕ) :
    tsupport (mollify (physicalRadialMollifierKernel m) f)⊆closedBall 0 (S+2) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  exact hx (physicalRadialMollify_eq_zero_outside hs m (lt_of_not_ge hn))

theorem physical_radial_H2_mollification_components_eventually (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop, ‖physicalRadialMollifyLp m f-f‖<δ ∧
      (∀ k, ‖physicalRadialMollifyLp m (d k)-d k‖<δ) ∧
      (∀ k l, ‖physicalRadialMollifyLp m (e k l)-e k l‖<δ) := by
  have h0 : ∀ᶠ m : ℕ in atTop, ‖physicalRadialMollifyLp m f-f‖<δ := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.1 (physicalRadialMollifyLp_tendsto f) δ hδ
  have h1 : ∀ᶠ m : ℕ in atTop, ∀ k, ‖physicalRadialMollifyLp m (d k)-d k‖<δ := by
    apply eventually_all.mpr
    intro k
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.1 (physicalRadialMollifyLp_tendsto (d k)) δ hδ
  have h2 : ∀ᶠ m : ℕ in atTop, ∀ k l, ‖physicalRadialMollifyLp m (e k l)-e k l‖<δ := by
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro l
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.1 (physicalRadialMollifyLp_tendsto (e k l)) δ hδ
  exact h0.and (h1.and h2)

def PhysicalRadialSmoothMollificationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (S : ℝ) (m : ℕ) : Prop :=
  let u := mollify (physicalRadialMollifierKernel m) f
  let g := physicalRadialMollifyLp m f
  let dg := fun k => physicalRadialMollifyLp m (d k)
  let eg := fun k l => physicalRadialMollifyLp m (e k l)
  ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u⊆closedBall 0 (S+2) ∧
  (g : Configuration 2 → ℂ)=ᵐ[volume] u ∧
  (∀ k, (dg k : Configuration 2 → ℂ)=ᵐ[volume] smoothPartial u k) ∧
  (∀ k l, (eg k l : Configuration 2 → ℂ)=ᵐ[volume] smoothPartial (smoothPartial u k) l) ∧
  (∀ k, WeakPartial g (dg k) k) ∧ (∀ k l, WeakPartial (dg k) (eg k l) l)

theorem physical_radial_smooth_mollification_data (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {S : ℝ} (hs : ∀ᵐ y ∂volume, S<‖y‖ → f y=0) (m : ℕ) :
    PhysicalRadialSmoothMollificationData f d e S m := by
  have hsupp := physicalRadialMollify_tsupport hs m
  have hc : HasCompactSupport (mollify (physicalRadialMollifierKernel m) f) :=
    (isCompact_closedBall (0 : Configuration 2) (S+2)).of_isClosed_subset (isClosed_tsupport _) hsupp
  exact ⟨mollify_contDiff _ (physicalRadialMollifierKernel_contDiff m)
    (physicalRadialMollifierKernel_hasCompactSupport m) f,hc,hsupp,physicalRadialMollifyLp_ae m f,
    (fun k => physicalRadialMollifyLp_partial_ae (hd k) m),
    (fun k l => physicalRadialMollifyLp_second_ae (hd k) (he k l) m),
    (fun k => physicalRadialMollifyLp_weakPartial (hd k) m),
    (fun k l => physicalRadialMollifyLp_weakPartial (he k l) m)⟩

theorem physicalRadialCompactState_ae_support (f : SpatialL2 2) (R : ℝ) (hR : 0<R) :
    ∀ᵐ x ∂volume, 2*R<‖x‖ → physicalRadialCompactState R hR f x=0 := by
  filter_upwards [physicalRadialCompactState_ae R hR f] with x hx
  intro hn
  rw [hx,physicalRadialCompactCutoff_eq_zero hR (by linarith),zero_smul]

#print axioms physicalRadialMollifyLp_isometry
#print axioms physicalRadialMollify_real
#print axioms physical_radial_H2_mollification_components_eventually
#print axioms physical_radial_smooth_mollification_data
end ManyBody.S8
