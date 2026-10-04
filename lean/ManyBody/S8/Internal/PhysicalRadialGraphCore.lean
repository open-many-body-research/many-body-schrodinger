import ManyBody.S8.Internal.PhysicalH2GraphCore
import ManyBody.S8.CoulombNormalizedRadialSmoothApproximation
import ManyBody.S8.CoulombSmoothCompactGraphDensity

/-! Actual radial smooth physical H2 density for arbitrary graph states, and
real inverse-norm symmetry/Rayleigh algebra. No eigenvalue or tail premise. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_radial_compact_H2_defect_arbitrarily_small (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ R : ℝ, ∃ hR : 1≤R,
      physicalRadialCompactH2DefectNorm R (lt_of_lt_of_le zero_lt_one hR) f d e≤δ := by
  obtain ⟨B1,B2,hB1,hB2,hbound⟩ := physicalRadialCompactCutoff_derivative_bounds
  let K := 7*(1+2*B1+B2)
  have hK : 0≤K := by dsimp [K]; positivity
  let t := δ/(7*(1+K))
  have ht : 0<t := by dsimp [t]; positivity
  obtain ⟨n,hn,h0,h1,h2⟩ :=
    ((eventually_ge_atTop (1:ℕ)).and (physical_H2_exterior_components_eventually f d e ht)).exists
  have hR : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have htail : weakH2ExteriorNorm f d e (n:ℝ)≤7*t := by
    exact physicalH2ComponentNorm_le_common (exteriorL2 (n:ℝ) f)
      (fun k => exteriorL2 (n:ℝ) (d k)) (fun k l => exteriorL2 (n:ℝ) (e k l))
      t ht.le h0.le (fun k => (h1 k).le) (fun k l => (h2 k l).le)
  have htid : (7*t)*(1+K)=δ := by
    dsimp [t]
    field_simp
  refine ⟨(n:ℝ),hR,?_⟩
  calc _≤K*weakH2ExteriorNorm f d e (n:ℝ) :=
      physicalRadialCompactH2DefectNorm_le B1 B2 hB1 hB2 hbound f d e (n:ℝ) hR
       _≤K*(7*t) := mul_le_mul_of_nonneg_left htail hK
       _≤δ := by nlinarith


theorem physical_radial_smooth_compact_H2_approximation (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ R : ℝ, ∃ hR : 1≤R,
      let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
      let F := physicalRadialCompactState R hRp f
      let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
      let A := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
      ∀ᶠ m : ℕ in atTop,
        PhysicalRadialSmoothMollificationData F D A (2*R) m ∧
        physicalH2ComponentNorm (physicalRadialMollifyLp m F-f)
          (fun k => physicalRadialMollifyLp m (D k)-d k)
          (fun k l => physicalRadialMollifyLp m (A k l)-e k l)≤δ := by
  let η := δ/14
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨R,hR,hraw⟩ := physical_radial_compact_H2_defect_arbitrarily_small f d e hη
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  have hraw' : physicalH2ComponentNorm (F-f) (fun k => D k-d k)
      (fun k l => A k l-e k l)≤η := hraw
  have h0 := (physicalH2ComponentNorm_bounds (F-f) (fun k => D k-d k)
    (fun k l => A k l-e k l)).1.trans hraw'
  have h1 (k : Coordinate 2) :=
    (physicalH2ComponentNorm_first_le (F-f) (fun k => D k-d k)
      (fun k l => A k l-e k l) k).trans hraw'
  have h2 (k l : Coordinate 2) :=
    ((physicalH2ComponentNorm_bounds (F-f) (fun k => D k-d k)
      (fun k l => A k l-e k l)).2.2 k l).trans hraw'
  have hdF (k : Coordinate 2) : WeakPartial F (D k) k :=
    physicalRadialCompactFirst_weakPartial (hd k) R hRp
  have heF (k l : Coordinate 2) : WeakPartial (D k) (A k l) l :=
    physicalRadialCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hRp
  refine ⟨R,hR,?_⟩
  filter_upwards [physical_radial_H2_mollification_components_eventually F D A hη] with m hm
  rcases hm with ⟨hm0,hm1,hm2⟩
  have htri (v w t : SpatialL2 2) (hv : ‖v-w‖<η) (hw : ‖w-t‖≤η) :
      ‖v-t‖≤2*η := by
    calc _≤‖v-w‖+‖w-t‖ := by simpa only [dist_eq_norm] using dist_triangle v w t
         _≤η+η := add_le_add hv.le hw
         _=2*η := by ring
  refine ⟨physical_radial_smooth_mollification_data F D A hdF heF
    (physicalRadialCompactState_ae_support f R hRp) m,?_⟩
  calc
    _≤7*(2*η) := by
      exact physicalH2ComponentNorm_le_common _ _ _ (2*η) (by positivity)
        (htri _ _ _ hm0 h0) (fun k => htri _ _ _ (hm1 k) (h1 k))
        (fun k l => htri _ _ _ (hm2 k l) (h2 k l))
    _=δ := by dsimp [η]; ring


theorem normalized_physical_pair_rayleigh_difference {f v h H : SpatialL2 2}
    (hv : ‖v‖=1) :
    |(inner ℂ v H).re-(inner ℂ f h).re|≤‖H-h‖+‖v-f‖*‖h‖ := by
  have hid : inner ℂ v H-inner ℂ f h=inner ℂ v (H-h)+inner ℂ (v-f) h := by
    rw [inner_sub_right,inner_sub_left]
    abel
  calc _=|(inner ℂ v H-inner ℂ f h).re| := by rw [Complex.sub_re]
       _≤‖inner ℂ v H-inner ℂ f h‖ := Complex.abs_re_le_norm _
       _≤‖inner ℂ v (H-h)‖+‖inner ℂ (v-f) h‖ := by rw [hid]; exact norm_add_le _ _
       _≤‖v‖*‖H-h‖+‖v-f‖*‖h‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
       _=‖H-h‖+‖v-f‖*‖h‖ := by rw [hv,one_mul]

theorem physical_radial_normalized_smooth_symmetries {f : SpatialL2 2}
    (hs : pullback twoElectronSwap f=f) (hr : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f)
    (R : ℝ) (hR : 0<R) (m : ℕ) :
    let F := physicalRadialCompactState R hR f
    let g := physicalRadialMollifyLp m F
    let c := physicalNormalizationScalar g
    let v := c • g
    let u := fun x => c • mollify (physicalRadialMollifierKernel m) F x
    pullback twoElectronSwap v=v ∧ (∀ᵐ x, (v x).im=0) ∧
    (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q v=v) ∧
    (∀ x, u (permuteSpace twoElectronSwap x)=u x) ∧
    (∀ x, (u x).im=0) ∧
    (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, u (configurationRotation 2 Q x)=u x) := by
  let F := physicalRadialCompactState R hR f
  let g := physicalRadialMollifyLp m F
  let c := physicalNormalizationScalar g
  have hFs : pullback twoElectronSwap F=F := physicalRadialCompactState_permutation twoElectronSwap hs R hR
  have hFr : ∀ᵐ x, (F x).im=0 := physicalRadialCompactState_real hr R hR
  have hFQ (Q : Position ≃ₗᵢ[ℝ] Position) : spatialRotation 2 Q F=F :=
    physicalRadialCompactState_rotation Q (hrot Q) R hR
  refine ⟨physical_normalization_permutation twoElectronSwap
      (physicalRadialMollifyLp_permutation m twoElectronSwap hFs),
    physical_normalization_real (physicalRadialMollifyLp_real m hFr),
    (fun Q => physical_normalization_rotation Q (physicalRadialMollifyLp_rotation m Q (hFQ Q))),?_,?_,?_⟩
  · intro x
    exact congrArg (fun z : ℂ => c • z)
      (physicalRadialMollify_isometry m (permuteSpace twoElectronSwap) hFs x)
  · intro x
    change (c • mollify (physicalRadialMollifierKernel m) F x).im=0
    have hreal := physicalRadialMollify_real m hFr x
    simp only [c,physicalNormalizationScalar,smul_eq_mul,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,hreal,mul_zero,zero_mul,add_zero]
  · intro Q x
    exact congrArg (fun z : ℂ => c • z)
      (physicalRadialMollify_isometry m (configurationRotation 2 Q) (hFQ Q) x)

#print axioms physical_radial_compact_H2_defect_arbitrarily_small
#print axioms physical_radial_smooth_compact_H2_approximation
#print axioms normalized_physical_pair_rayleigh_difference
#print axioms physical_radial_normalized_smooth_symmetries
end ManyBody.S8
