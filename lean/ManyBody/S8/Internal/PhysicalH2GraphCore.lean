import ManyBody.S8.Internal.PhysicalSmoothH2Mollification
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! General physical H2 domain density through genuine compact truncation and
mollification. No ground-state, eigenvalue or decay premise is added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators ENNReal
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_exterior_L2_norm_tendsto_zero {N : ℕ} (f : SpatialL2 N) :
    Tendsto (fun n : ℕ => ‖exteriorL2 (n:ℝ) f‖) atTop (𝓝 0) := by
  let g (n : ℕ) : Configuration N → ℂ :=
    {x : Configuration N | (n:ℝ)≤‖x‖}.indicator (fun x => f x)
  let G (n : ℕ) (x : Configuration N) : ℝ≥0∞ := ‖g n x‖ₑ^(2:ℝ)
  have hgm (n : ℕ) : MemLp (g n) 2 volume :=
    (Lp.memLp f).indicator (measurableSet_le measurable_const continuous_norm.measurable)
  have hm (n : ℕ) : AEMeasurable (G n) volume :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hgm n).aemeasurable.enorm
  have hb (n : ℕ) : G n ≤ᵐ[volume] fun x => ‖f x‖ₑ^(2:ℝ) := by
    apply ae_of_all
    intro x
    by_cases h : (n:ℝ)≤‖x‖
    · simp [G,g,h]
    · simp [G,g,h]
  have hi : (∫⁻ x : Configuration N, ‖f x‖ₑ^(2:ℝ) ∂volume)≠⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p:=(2:ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp f).2
    simpa using h.ne
  have ht : ∀ᵐ x : Configuration N, Tendsto (fun n => G n x) atTop (𝓝 0) := by
    apply ae_of_all
    intro x
    have he : ∀ᶠ n : ℕ in atTop, ‖x‖<(n:ℝ) :=
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_gt_atTop ‖x‖)
    have hz : (fun n => G n x)=ᶠ[atTop] fun _ => 0 := by
      filter_upwards [he] with n hn
      simp [G,g,not_le.mpr hn]
    exact tendsto_const_nhds.congr' hz.symm
  have hI : Tendsto (fun n => ∫⁻ x, G n x ∂volume) atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence' (fun x => ‖f x‖ₑ^(2:ℝ)) hm hb hi ht
  have hP : Tendsto (fun n => (∫⁻ x, G n x ∂volume)^(1/(2:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ((ENNReal.continuous_rpow_const (y:=1/(2:ℝ))).tendsto (0:ℝ≥0∞)).comp hI
  have hLp : Tendsto (fun n => eLpNorm (g n) 2 volume) atTop (𝓝 0) := by
    simpa only [G,eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠⊤),ENNReal.toReal_ofNat] using hP
  have hreal : Tendsto (fun n => (eLpNorm (g n) 2 volume).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞)≠⊤)).comp hLp
  convert hreal using 1
  funext n
  rw [Lp.norm_def]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae (exteriorL2_ae (n:ℝ) f))


theorem physical_H2_exterior_components_eventually {N : ℕ} (f : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop, ‖exteriorL2 (n:ℝ) f‖<δ ∧
      (∀ k, ‖exteriorL2 (n:ℝ) (d k)‖<δ) ∧
      (∀ k l, ‖exteriorL2 (n:ℝ) (e k l)‖<δ) := by
  have h0 := (physical_exterior_L2_norm_tendsto_zero f).eventually (eventually_lt_nhds hδ)
  have h1 : ∀ᶠ n : ℕ in atTop, ∀ k, ‖exteriorL2 (n:ℝ) (d k)‖<δ := by
    apply eventually_all.mpr
    intro k
    exact (physical_exterior_L2_norm_tendsto_zero (d k)).eventually (eventually_lt_nhds hδ)
  have h2 : ∀ᶠ n : ℕ in atTop, ∀ k l, ‖exteriorL2 (n:ℝ) (e k l)‖<δ := by
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro l
    exact (physical_exterior_L2_norm_tendsto_zero (e k l)).eventually (eventually_lt_nhds hδ)
  exact h0.and (h1.and h2)

theorem physical_compact_H2_defect_arbitrarily_small (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ R : ℝ, ∃ hR : 1≤R,
      physicalCompactH2DefectNorm R (lt_of_lt_of_le zero_lt_one hR) f d e≤δ := by
  obtain ⟨B1,B2,hB1,hB2,hbound⟩ := physicalCompactCutoff_derivative_bounds
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
      physicalCompactH2DefectNorm_le B1 B2 hB1 hB2 hbound f d e (n:ℝ) hR
       _≤K*(7*t) := mul_le_mul_of_nonneg_left htail hK
       _≤δ := by nlinarith


theorem physical_smooth_compact_H2_approximation (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ R : ℝ, ∃ hR : 1≤R,
      let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
      let F := physicalCompactState R hRp f
      let D := fun k => physicalCompactFirst R hRp f (d k) k
      let A := fun k l => physicalCompactSecond R hRp f (d k) (d l) (e k l) k l
      ∀ᶠ m : ℕ in atTop,
        PhysicalSmoothMollificationData F D A (2*R) m ∧
        physicalH2ComponentNorm (mollifyLp m F-f)
          (fun k => mollifyLp m (D k)-d k)
          (fun k l => mollifyLp m (A k l)-e k l)≤δ := by
  let η := δ/14
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨R,hR,hraw⟩ := physical_compact_H2_defect_arbitrarily_small f d e hη
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalCompactState R hRp f
  let D := fun k => physicalCompactFirst R hRp f (d k) k
  let A := fun k l => physicalCompactSecond R hRp f (d k) (d l) (e k l) k l
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
    physicalCompactFirst_weakPartial (hd k) R hRp
  have heF (k l : Coordinate 2) : WeakPartial (D k) (A k l) l :=
    physicalCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hRp
  refine ⟨R,hR,?_⟩
  filter_upwards [physical_H2_mollification_components_eventually F D A hη] with m hm
  rcases hm with ⟨hm0,hm1,hm2⟩
  have htri (v w t : SpatialL2 2) (hv : ‖v-w‖<η) (hw : ‖w-t‖≤η) :
      ‖v-t‖≤2*η := by
    calc _≤‖v-w‖+‖w-t‖ := by simpa only [dist_eq_norm] using dist_triangle v w t
         _≤η+η := add_le_add hv.le hw
         _=2*η := by ring
  refine ⟨physical_smooth_mollification_data F D A hdF heF
    (physicalCompactState_ae_support f R hRp) m,?_⟩
  calc
    _≤7*(2*η) := by
      exact physicalH2ComponentNorm_le_common _ _ _ (2*η) (by positivity)
        (htri _ _ _ hm0 h0) (fun k => htri _ _ _ (hm1 k) (h1 k))
        (fun k l => htri _ _ _ (hm2 k l) (h2 k l))
    _=δ := by dsimp [η]; ring

#print axioms physical_exterior_L2_norm_tendsto_zero
#print axioms physical_H2_exterior_components_eventually
#print axioms physical_compact_H2_defect_arbitrarily_small
#print axioms physical_smooth_compact_H2_approximation
end ManyBody.S8
