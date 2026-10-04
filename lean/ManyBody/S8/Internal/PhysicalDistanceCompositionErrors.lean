import ManyBody.S8.Internal.LocalPhysicalDistanceWeakH2
import ManyBody.S8.Internal.PhysicalDistanceH2ErrorBudget
import Mathlib.Tactic
/-! Actual compact physical H2 error budgets from true local distance-profile C2 errors. Original weak derivatives are derived by regularized closure, all43 L2 component bounds use the genuine compact inverse-distance class, and the cutoff constant is chosen before the profile and error tolerance. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum
theorem physical_distance_first_bound {g : (Fin 3 → ℝ) → ℂ}
    {C : ℝ} {x v : Configuration 2}
    (hD : ‖fderiv ℝ g (physicalDistanceTriple x)‖≤C)
    (hv : ‖v‖≤1) : ‖physicalDistanceCompositionFirst g x v‖≤2*C := by
  have ha := physical_distance_gradient_norm_le x v
  have hb := (fderiv ℝ g (physicalDistanceTriple x)).le_opNorm
    (physicalDistanceGradient x v)
  dsimp [physicalDistanceCompositionFirst]
  nlinarith [norm_nonneg (fderiv ℝ g (physicalDistanceTriple x)),
    norm_nonneg (physicalDistanceGradient x v)]

theorem physical_distance_second_bound {g : (Fin 3 → ℝ) → ℂ}
    {C : ℝ} {x v w : Configuration 2} (hx : collisionFree x)
    (hD : ‖fderiv ℝ g (physicalDistanceTriple x)‖≤C)
    (hDD : ‖fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)‖≤C)
    (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖physicalDistanceCompositionSecond g x v w‖≤4*C+8*C*physicalInverseDistanceBudget x := by
  have ha := physical_distance_gradient_norm_le x v
  have hb := physical_distance_gradient_norm_le x w
  have ht := bounded_bilinear_apply _ hDD (hb.trans (by linarith)) (ha.trans (by linarith))
    (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤2)
  have hi := physical_distance_hessian_norm_le hx v w
  have hB : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun _ _ => by positivity
  have hprod : ‖v‖*‖w‖≤1 := by nlinarith [norm_nonneg v,norm_nonneg w]
  have hi' : ‖physicalDistanceHessian x v w‖≤8*physicalInverseDistanceBudget x := by
    nlinarith
  have hs := (fderiv ℝ g (physicalDistanceTriple x)).le_opNorm
    (physicalDistanceHessian x v w)
  have hs' : ‖fderiv ℝ g (physicalDistanceTriple x)
      (physicalDistanceHessian x v w)‖≤8*C*physicalInverseDistanceBudget x := by
    have h0 := mul_le_mul hD hi' (norm_nonneg _) (by linarith [norm_nonneg (fderiv ℝ g (physicalDistanceTriple x))])
    nlinarith
  unfold physicalDistanceCompositionSecond
  exact (norm_add_le _ _).trans (by nlinarith)


theorem physical_cutoff_distance_bounds {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {C D : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hC : PhysicalCutoffJetBound χ C) (hD : 0≤D)
    {x v w : Configuration 2} (hx : collisionFree x) (hv : ‖v‖≤1) (hw : ‖w‖≤1)
    (hg : ‖g (physicalDistanceTriple x)‖≤D)
    (hg1 : ‖fderiv ℝ g (physicalDistanceTriple x)‖≤D)
    (hg2 : ‖fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)‖≤D) :
    ‖physicalCutoffDistanceValue χ g x‖≤C*D ∧
    ‖physicalCutoffDistanceFirst χ g x v‖≤3*C*D ∧
    ‖physicalCutoffDistanceSecond χ g x v w‖≤16*C*D*(1+physicalInverseDistanceBudget x) := by
  have hC0 : 0≤C := le_trans (by norm_num) hC.1
  obtain ⟨hc,hcv,hcw,hcvw⟩ := actual_cutoff_directional_jet_bound hχ hC x hv hw
  have hf := physical_distance_first_bound hg1 hv
  have hfw := physical_distance_first_bound hg1 hw
  have hs := physical_distance_second_bound hx hg1 hg2 hv hw
  have hB : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨actual_norm_smul_bound hc hg hC0,?_,?_⟩
  · unfold physicalCutoffDistanceFirst
    exact (norm_add_le _ _).trans ((add_le_add (actual_norm_smul_bound hc hf hC0)
      (actual_norm_smul_bound hcv hg hC0)).trans (by ring_nf; rfl))
  · unfold physicalCutoffDistanceSecond
    calc
      _ ≤ ‖χ x • physicalDistanceCompositionSecond g x v w‖+
          ‖fderiv ℝ χ x w • physicalDistanceCompositionFirst g x v‖+
          ‖fderiv ℝ χ x v • physicalDistanceCompositionFirst g x w‖+
          ‖fderiv ℝ (fun y => fderiv ℝ χ y v) x w • g (physicalDistanceTriple x)‖ :=
        actual_complex_four_sum_norm_le _ _ _ _
      _ ≤ C*(4*D+8*D*physicalInverseDistanceBudget x)+C*(2*D)+C*(2*D)+C*D :=
        add_le_add (add_le_add (add_le_add (actual_norm_smul_bound hc hs hC0)
          (actual_norm_smul_bound hcw hf hC0)) (actual_norm_smul_bound hcv hfw hC0))
          (actual_norm_smul_bound hcvw hg hC0)
      _ ≤ 16*C*D*(1+physicalInverseDistanceBudget x) := by
        nlinarith [mul_nonneg hC0 hD,mul_nonneg (mul_nonneg hC0 hD) hB]

theorem physical_cutoff_distance_jets_zero_off {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {x : Configuration 2} (hx : x∉tsupport χ)
    (v w : Configuration 2) :
    physicalCutoffDistanceValue χ g x=0 ∧
    physicalCutoffDistanceFirst χ g x v=0 ∧
    physicalCutoffDistanceSecond χ g x v w=0 := by
  obtain ⟨h0,hv,hw,hvw⟩ := cutoff_directional_jets_zero_off_tsupport hx v w
  simp only [physicalCutoffDistanceValue,physicalCutoffDistanceFirst,
    physicalCutoffDistanceSecond,h0,hv,hw,hvw,zero_smul,add_zero, and_self]


theorem physical_cutoff_distance_indicator_bounds {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {C D : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hC : PhysicalCutoffJetBound χ C) (hD : 0≤D)
    (hg : ∀x∈tsupport χ, ‖g (physicalDistanceTriple x)‖≤D ∧
      ‖fderiv ℝ g (physicalDistanceTriple x)‖≤D ∧
      ‖fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)‖≤D)
    {x v w : Configuration 2} (hx : collisionFree x) (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖physicalCutoffDistanceValue χ g x‖≤
      ‖(tsupport χ).indicator (fun y => 16*C*D*(1+physicalInverseDistanceBudget y)) x‖ ∧
    ‖physicalCutoffDistanceFirst χ g x v‖≤
      ‖(tsupport χ).indicator (fun y => 16*C*D*(1+physicalInverseDistanceBudget y)) x‖ ∧
    ‖physicalCutoffDistanceSecond χ g x v w‖≤
      ‖(tsupport χ).indicator (fun y => 16*C*D*(1+physicalInverseDistanceBudget y)) x‖ := by
  by_cases hxs : x∈tsupport χ
  · obtain ⟨h0,h1,h2⟩ := hg x hxs
    obtain ⟨hv0,hv1,hv2⟩ := physical_cutoff_distance_bounds hχ hC hD hx hv hw h0 h1 h2
    have hB : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun _ _ => by positivity
    have hC0 : 0≤C := (by norm_num : (0:ℝ)≤1).trans hC.1
    have hCD : 0≤C*D := mul_nonneg hC0 hD
    rw [Set.indicator_of_mem hxs,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact ⟨hv0.trans (by nlinarith [mul_nonneg hCD hB]),
      hv1.trans (by nlinarith [mul_nonneg hCD hB]),hv2⟩
  · obtain ⟨h0,h1,h2⟩ := physical_cutoff_distance_jets_zero_off (g:=g) hxs v w
    simp only [h0,h1,h2,norm_zero,Set.indicator_of_notMem hxs,le_refl,and_self]



def PhysicalDistanceCutoffH2ErrorData (χ : Configuration 2 → ℝ) (hc : HasCompactSupport χ)
    (g : (Fin 3 → ℝ) → ℂ) (ζ C : ℝ) : Prop :=
  ∃F : SpatialL2 2, ∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
    F=ᵐ[volume] physicalCutoffDistanceValue χ g ∧
    (∀k,d k=ᵐ[volume] fun x => physicalCutoffDistanceFirst χ g x (coordinateVector k)) ∧
    (∀k j,e k j=ᵐ[volume] fun x => physicalCutoffDistanceSecond χ g x (coordinateVector k) (coordinateVector j)) ∧
    (∀k,WeakPartial F (d k) k) ∧ (∀k j,WeakPartial (d k) (e k j) j) ∧ HasH2 F ∧
    ‖F‖≤ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖ ∧
    (∀k,‖d k‖≤ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖) ∧
    (∀k j,‖e k j‖≤ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖) ∧
    physicalH2ComponentNorm F d e≤7*ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖ ∧
    ‖F‖+(∑k,‖d k‖)+(∑k,∑j,‖e k j‖)≤43*ζ*C*‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖

theorem physical_distance_cutoff_small_profile_H2_error
    {χ : Configuration 2 → ℝ} {g : (Fin 3 → ℝ) → ℂ} {ζ C : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hC : PhysicalCutoffJetBound χ C)
    (hζ : 0≤ζ) (hdata : PhysicalDistanceWeakH2Data χ g)
    (hg : ∀x∈tsupport χ, ‖g (physicalDistanceTriple x)‖≤ζ ∧
      ‖fderiv ℝ g (physicalDistanceTriple x)‖≤ζ ∧
      ‖fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)‖≤ζ) :
    PhysicalDistanceCutoffH2ErrorData χ hc g ζ (16*C) := by
  obtain ⟨F,d,e,hF,hd,he,hw1,hw2,hH2⟩ := hdata
  have hC0 : 0≤C := (by norm_num : (0:ℝ)≤1).trans hC.1
  have hscale (x : Configuration 2) :
      ‖(tsupport χ).indicator (fun y => 16*C*ζ*(1+physicalInverseDistanceBudget y)) x‖=
      ζ*(16*C)*‖(tsupport χ).indicator (fun y => 1+physicalInverseDistanceBudget y) x‖ := by
    by_cases hx : x∈tsupport χ
    · have hB : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun _ _ => by positivity
      rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      ring
    · simp only [Set.indicator_of_notMem hx,norm_zero,mul_zero]
  have hv (k : Coordinate 2) : ‖coordinateVector k‖≤1 := by simp [coordinateVector]
  have hbound (k j : Coordinate 2) : ∀ᵐx∂volume,
      ‖physicalCutoffDistanceValue χ g x‖≤ζ*(16*C)*‖(tsupport χ).indicator (fun y => 1+physicalInverseDistanceBudget y) x‖ ∧
      ‖physicalCutoffDistanceFirst χ g x (coordinateVector k)‖≤ζ*(16*C)*‖(tsupport χ).indicator (fun y => 1+physicalInverseDistanceBudget y) x‖ ∧
      ‖physicalCutoffDistanceSecond χ g x (coordinateVector k) (coordinateVector j)‖≤ζ*(16*C)*‖(tsupport χ).indicator (fun y => 1+physicalInverseDistanceBudget y) x‖ := by
    filter_upwards [ae_collisionFree 2] with x hx
    have hh := physical_cutoff_distance_indicator_bounds hχ hC hζ hg hx (hv k) (hv j)
    rwa [hscale] at hh
  have h0 : ∀ᵐx∂volume,‖F x‖≤ζ*(16*C)*‖(tsupport χ).indicator (fun y => 1+physicalInverseDistanceBudget y) x‖ := by
    filter_upwards [hF,hbound (0,0) (0,0)] with x hx hy
    rw [hx]
    exact hy.1
  have h1 (k : Coordinate 2) : ∀ᵐx∂volume,‖d k x‖≤ζ*(16*C)*‖(tsupport χ).indicator (fun y => 1+physicalInverseDistanceBudget y) x‖ := by
    filter_upwards [hd k,hbound k (0,0)] with x hx hy
    rw [hx]
    exact hy.2.1
  have h2 (k j : Coordinate 2) : ∀ᵐx∂volume,‖e k j x‖≤ζ*(16*C)*‖(tsupport χ).indicator (fun y => 1+physicalInverseDistanceBudget y) x‖ := by
    filter_upwards [he k j,hbound k j] with x hx hy
    rw [hx]
    exact hy.2.2
  exact ⟨F,d,e,hF,hd,he,hw1,hw2,hH2,
    physical_distance_43_component_error_budget hc F d e hζ (by positivity) h0 h1 h2⟩

theorem actual_local_physical_distance_cutoff_H2_error
    {χ : Configuration 2 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃C : ℝ, 1≤C ∧ ∀(g : (Fin 3 → ℝ) → ℂ) (a : Fin 3 → ℝ) (R ζ : ℝ),
      0<R → 0≤ζ → ContDiffOn ℝ ∞ g (ball a R) →
      (∀x∈tsupport χ,physicalDistanceTriple x∈closedBall a (R/8)) →
      (∀x∈tsupport χ, ‖g (physicalDistanceTriple x)‖≤ζ ∧
        ‖fderiv ℝ g (physicalDistanceTriple x)‖≤ζ ∧
        ‖fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x)‖≤ζ) →
      PhysicalDistanceCutoffH2ErrorData χ hc g ζ C := by
  obtain ⟨Cχ,hCχ⟩ := actual_compact_cutoff_jet_bound hχ hc
  refine ⟨16*Cχ,by linarith [hCχ.1],?_⟩
  intro g a R ζ hR hζ hg hs hb
  exact physical_distance_cutoff_small_profile_H2_error hχ hc hCχ hζ
    (actual_local_physical_distance_cutoff_weakH2 hχ hc hR hg hs) hb

#print axioms actual_local_physical_distance_cutoff_H2_error
#print axioms physical_cutoff_distance_indicator_bounds
end ManyBody.S8