import ManyBody.S8.Internal.PhysicalCutoffDistanceJets
import ManyBody.S8.Internal.PhysicalCompactL2Domination
import Mathlib.Tactic
/-! Genuine compact cutoff jet bounds and uniform physical inverse-distance domination of the actual smooth regularized composition jets. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalCutoffJetBound (χ : Configuration 2 → ℝ) (C : ℝ) : Prop :=
  1≤C ∧ ∀x, ‖χ x‖≤C ∧ ‖fderiv ℝ χ x‖≤C ∧ ‖fderiv ℝ (fderiv ℝ χ) x‖≤C

theorem actual_compact_cutoff_jet_bound {χ : Configuration 2 → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃C, PhysicalCutoffJetBound χ C := by
  have hd : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  have heNorm : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ χ) x‖) := by
    have hi : Continuous (iteratedFDeriv ℝ 2 χ) := continuous_iff_continuousAt.mpr
      (fun x => hχ.contDiffAt.continuousAt_iteratedFDeriv (by simp))
    have heq : (fun x => ‖fderiv ℝ (fderiv ℝ χ) x‖)=(fun x => ‖iteratedFDeriv ℝ 2 χ x‖) := by
      funext x
      rw [←norm_iteratedFDeriv_one (fderiv ℝ χ),norm_iteratedFDeriv_fderiv]
    rw [heq]
    exact hi.norm
  have hK : IsCompact (tsupport χ) := hc
  obtain ⟨C0,h0⟩ := hK.exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨C1,h1⟩ := hK.exists_bound_of_continuousOn hd.continuousOn
  obtain ⟨C2,h2norm⟩ := hK.exists_bound_of_continuousOn heNorm.continuousOn
  have h2 : ∀x∈tsupport χ,‖fderiv ℝ (fderiv ℝ χ) x‖≤C2 := by
    intro x hx
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h2norm x hx)
  let C : ℝ := max 1 (max C0 (max C1 C2))
  have hC0 : C0≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hC1 : C1≤C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC2 : C2≤C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  refine ⟨C,le_max_left _ _,?_⟩
  intro x
  by_cases hx : x∈tsupport χ
  · exact ⟨(h0 x hx).trans hC0,(h1 x hx).trans hC1,(h2 x hx).trans hC2⟩
  · have h0x := image_eq_zero_of_notMem_tsupport hx
    have h1x := fderiv_of_notMem_tsupport ℝ hx
    have hs : x∉tsupport (fderiv ℝ χ) := fun hy => hx (tsupport_fderiv_subset ℝ hy)
    have h2x := fderiv_of_notMem_tsupport ℝ hs
    have h2z : ‖fderiv ℝ (fderiv ℝ χ) x‖=0 := by
      rw [h2x]
      change ‖(0 : Configuration 2 →L[ℝ] Configuration 2 →L[ℝ] ℝ)‖=0
      exact ContinuousLinearMap.opNorm_zero
    simp only [h0x,h1x,h2z,norm_zero,and_self]
    exact hC
theorem bounded_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E→L[ℝ]F) {C : ℝ} (hL : ‖L‖≤C) {v : E} (hv : ‖v‖≤1) :
    ‖L v‖≤C := by
  exact (L.le_opNorm v).trans (by nlinarith [norm_nonneg L,norm_nonneg v])

theorem bounded_bilinear_apply {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E→L[ℝ]F→L[ℝ]G) {C a b : ℝ} (hL : ‖L‖≤C)
    {v : E} {w : F} (hv : ‖v‖≤a) (hw : ‖w‖≤b) (ha : 0≤a) (hb : 0≤b) :
    ‖L v w‖≤C*a*b := by
  have hi := (L.le_opNorm v)
  have hj := (L v).le_opNorm w
  have hk := mul_le_mul_of_nonneg_right hi (norm_nonneg w)
  have ht := mul_le_mul hv hw (norm_nonneg w) ha
  have hu := mul_le_mul_of_nonneg_left ht (norm_nonneg L)
  have hl := mul_le_mul_of_nonneg_right hL (mul_nonneg ha hb)
  nlinarith

theorem actual_cutoff_directional_jet_bound {χ : Configuration 2 → ℝ} {C : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hC : PhysicalCutoffJetBound χ C) (x : Configuration 2)
    {v w : Configuration 2} (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖χ x‖≤C ∧ ‖fderiv ℝ χ x v‖≤C ∧ ‖fderiv ℝ χ x w‖≤C ∧
      ‖fderiv ℝ (fun y => fderiv ℝ χ y v) x w‖≤C := by
  refine ⟨(hC.2 x).1,bounded_clm_apply _ (hC.2 x).2.1 hv,
    bounded_clm_apply _ (hC.2 x).2.1 hw,?_⟩
  have he : fderiv ℝ (fun y => fderiv ℝ χ y v) x w=
      fderiv ℝ (fderiv ℝ χ) x w v := by
    have hh := (((hχ.fderiv_right (m:=∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
      (hasFDerivAt_const v x)).fderiv
    simpa using congrArg (fun L => L w) hh
  rw [he]
  simpa using bounded_bilinear_apply _ (hC.2 x).2.2 hw hv (by norm_num) (by norm_num)

theorem regularized_distance_first_bound {g : (Fin 3 → ℝ) → ℂ} {δ : ℝ}
    (hδ : 0<δ) {C : ℝ} {x v : Configuration 2}
    (hD : ‖fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)‖≤C)
    (hv : ‖v‖≤1) : ‖regularizedDistanceCompositionFirst g δ x v‖≤2*C := by
  have ha := regularized_physical_distance_gradient_norm_le hδ x v
  have hb := (fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)).le_opNorm
    (regularizedPhysicalDistanceGradient δ x v)
  dsimp [regularizedDistanceCompositionFirst]
  nlinarith [norm_nonneg (fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)),
    norm_nonneg (regularizedPhysicalDistanceGradient δ x v)]

theorem regularized_distance_second_bound {g : (Fin 3 → ℝ) → ℂ} {δ : ℝ}
    (hδ : 0<δ) {C : ℝ} {x v w : Configuration 2} (hx : collisionFree x)
    (hD : ‖fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)‖≤C)
    (hDD : ‖fderiv ℝ (fderiv ℝ g) (regularizedPhysicalDistanceTriple δ x)‖≤C)
    (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖regularizedDistanceCompositionSecond g δ x v w‖≤4*C+8*C*physicalInverseDistanceBudget x := by
  have ha := regularized_physical_distance_gradient_norm_le hδ x v
  have hb := regularized_physical_distance_gradient_norm_le hδ x w
  have ht := bounded_bilinear_apply _ hDD (hb.trans (by linarith)) (ha.trans (by linarith))
    (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤2)
  have hi := regularized_physical_distance_hessian_norm_le hδ hx v w
  have hB : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun _ _ => by positivity
  have hprod : ‖v‖*‖w‖≤1 := by nlinarith [norm_nonneg v,norm_nonneg w]
  have hi' : ‖regularizedPhysicalDistanceHessian δ x v w‖≤8*physicalInverseDistanceBudget x := by
    nlinarith
  have hs := (fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)).le_opNorm
    (regularizedPhysicalDistanceHessian δ x v w)
  have hs' : ‖fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)
      (regularizedPhysicalDistanceHessian δ x v w)‖≤8*C*physicalInverseDistanceBudget x := by
    have h0 := mul_le_mul hD hi' (norm_nonneg _) (by linarith [norm_nonneg (fderiv ℝ g (regularizedPhysicalDistanceTriple δ x))])
    nlinarith
  unfold regularizedDistanceCompositionSecond
  exact (norm_add_le _ _).trans (by nlinarith)


theorem actual_complex_four_sum_norm_le (a b c d : ℂ) :
    ‖a+b+c+d‖≤‖a‖+‖b‖+‖c‖+‖d‖ := by
  linarith [norm_add_le a b,norm_add_le (a+b) c,norm_add_le (a+b+c) d]

theorem actual_norm_smul_bound {a : ℝ} {z : ℂ} {C D : ℝ}
    (ha : ‖a‖≤C) (hz : ‖z‖≤D) (hC : 0≤C) : ‖a • z‖≤C*D := by
  rw [norm_smul]
  exact mul_le_mul ha hz (norm_nonneg z) hC

theorem regularized_cutoff_distance_bounds {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {δ C D : ℝ} (hδ : 0<δ)
    (hχ : ContDiff ℝ ∞ χ) (hC : PhysicalCutoffJetBound χ C) (hD : 0≤D)
    {x v w : Configuration 2} (hx : collisionFree x) (hv : ‖v‖≤1) (hw : ‖w‖≤1)
    (hg : ‖g (regularizedPhysicalDistanceTriple δ x)‖≤D)
    (hg1 : ‖fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)‖≤D)
    (hg2 : ‖fderiv ℝ (fderiv ℝ g) (regularizedPhysicalDistanceTriple δ x)‖≤D) :
    ‖regularizedCutoffDistanceValue χ g δ x‖≤C*D ∧
    ‖regularizedCutoffDistanceFirst χ g δ x v‖≤3*C*D ∧
    ‖regularizedCutoffDistanceSecond χ g δ x v w‖≤16*C*D*(1+physicalInverseDistanceBudget x) := by
  have hC0 : 0≤C := le_trans (by norm_num) hC.1
  obtain ⟨hc,hcv,hcw,hcvw⟩ := actual_cutoff_directional_jet_bound hχ hC x hv hw
  have hf := regularized_distance_first_bound hδ hg1 hv
  have hfw := regularized_distance_first_bound hδ hg1 hw
  have hs := regularized_distance_second_bound hδ hx hg1 hg2 hv hw
  have hB : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨actual_norm_smul_bound hc hg hC0,?_,?_⟩
  · unfold regularizedCutoffDistanceFirst
    exact (norm_add_le _ _).trans ((add_le_add (actual_norm_smul_bound hc hf hC0)
      (actual_norm_smul_bound hcv hg hC0)).trans (by ring_nf; rfl))
  · unfold regularizedCutoffDistanceSecond
    calc
      _ ≤ ‖χ x • regularizedDistanceCompositionSecond g δ x v w‖+
          ‖fderiv ℝ χ x w • regularizedDistanceCompositionFirst g δ x v‖+
          ‖fderiv ℝ χ x v • regularizedDistanceCompositionFirst g δ x w‖+
          ‖fderiv ℝ (fun y => fderiv ℝ χ y v) x w • g (regularizedPhysicalDistanceTriple δ x)‖ :=
        actual_complex_four_sum_norm_le _ _ _ _
      _ ≤ C*(4*D+8*D*physicalInverseDistanceBudget x)+C*(2*D)+C*(2*D)+C*D :=
        add_le_add (add_le_add (add_le_add (actual_norm_smul_bound hc hs hC0)
          (actual_norm_smul_bound hcw hf hC0)) (actual_norm_smul_bound hcv hfw hC0))
          (actual_norm_smul_bound hcvw hg hC0)
      _ ≤ 16*C*D*(1+physicalInverseDistanceBudget x) := by
        nlinarith [mul_nonneg hC0 hD,mul_nonneg (mul_nonneg hC0 hD) hB]

theorem cutoff_directional_jets_zero_off_tsupport {χ : Configuration 2 → ℝ}
    {x : Configuration 2} (hx : x∉tsupport χ) (v w : Configuration 2) :
    χ x=0 ∧ fderiv ℝ χ x v=0 ∧ fderiv ℝ χ x w=0 ∧
      fderiv ℝ (fun y => fderiv ℝ χ y v) x w=0 := by
  have hd := fderiv_of_notMem_tsupport ℝ hx
  have hs : x∉tsupport (fun y => fderiv ℝ χ y v) :=
    fun hh => hx (tsupport_fderiv_apply_subset ℝ v hh)
  have he := fderiv_of_notMem_tsupport ℝ hs
  exact ⟨image_eq_zero_of_notMem_tsupport hx,by simp [hd],by simp [hd],by simp [he]⟩

theorem regularized_cutoff_distance_jets_zero_off {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {x : Configuration 2} (hx : x∉tsupport χ)
    (δ : ℝ) (v w : Configuration 2) :
    regularizedCutoffDistanceValue χ g δ x=0 ∧
    regularizedCutoffDistanceFirst χ g δ x v=0 ∧
    regularizedCutoffDistanceSecond χ g δ x v w=0 := by
  obtain ⟨h0,hv,hw,hvw⟩ := cutoff_directional_jets_zero_off_tsupport hx v w
  simp only [regularizedCutoffDistanceValue,regularizedCutoffDistanceFirst,
    regularizedCutoffDistanceSecond,h0,hv,hw,hvw,zero_smul,add_zero, and_self]


theorem regularized_cutoff_distance_indicator_bounds {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {δ C D : ℝ} (hδ : 0<δ)
    (hχ : ContDiff ℝ ∞ χ) (hC : PhysicalCutoffJetBound χ C) (hD : 0≤D)
    (hg : ∀x∈tsupport χ, ‖g (regularizedPhysicalDistanceTriple δ x)‖≤D ∧
      ‖fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)‖≤D ∧
      ‖fderiv ℝ (fderiv ℝ g) (regularizedPhysicalDistanceTriple δ x)‖≤D)
    {x v w : Configuration 2} (hx : collisionFree x) (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖regularizedCutoffDistanceValue χ g δ x‖≤
      ‖(tsupport χ).indicator (fun y => 16*C*D*(1+physicalInverseDistanceBudget y)) x‖ ∧
    ‖regularizedCutoffDistanceFirst χ g δ x v‖≤
      ‖(tsupport χ).indicator (fun y => 16*C*D*(1+physicalInverseDistanceBudget y)) x‖ ∧
    ‖regularizedCutoffDistanceSecond χ g δ x v w‖≤
      ‖(tsupport χ).indicator (fun y => 16*C*D*(1+physicalInverseDistanceBudget y)) x‖ := by
  by_cases hxs : x∈tsupport χ
  · obtain ⟨h0,h1,h2⟩ := hg x hxs
    obtain ⟨hv0,hv1,hv2⟩ := regularized_cutoff_distance_bounds hδ hχ hC hD hx hv hw h0 h1 h2
    have hB : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun _ _ => by positivity
    have hC0 : 0≤C := (by norm_num : (0:ℝ)≤1).trans hC.1
    have hCD : 0≤C*D := mul_nonneg hC0 hD
    rw [Set.indicator_of_mem hxs,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact ⟨hv0.trans (by nlinarith [mul_nonneg hCD hB]),
      hv1.trans (by nlinarith [mul_nonneg hCD hB]),hv2⟩
  · obtain ⟨h0,h1,h2⟩ := regularized_cutoff_distance_jets_zero_off (g:=g) hxs δ v w
    simp only [h0,h1,h2,norm_zero,Set.indicator_of_notMem hxs,le_refl,and_self]

#print axioms regularized_cutoff_distance_indicator_bounds
#print axioms regularized_cutoff_distance_bounds
#print axioms actual_compact_cutoff_jet_bound
end ManyBody.S8