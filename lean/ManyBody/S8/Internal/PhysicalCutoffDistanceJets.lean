import ManyBody.S8.Internal.PhysicalDistanceCompositionClassical
import ManyBody.S8.Internal.PhysicalDistanceCompositionLimits
import HardyWeakCore_v1
import Mathlib.Tactic
/-! Actual cutoff product jets for the physical distance pullback and its smooth regularizations. Classical chain rules and collision-free jet convergence are proved here; no weak derivative or closure premise is supplied. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem actual_cutoff_first_fderiv {χ : Configuration 2 → ℝ}
    {f : Configuration 2 → ℂ} {x : Configuration 2}
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x)
    (v : Configuration 2) :
    fderiv ℝ (fun y => χ y • f y) x v =
      χ x • fderiv ℝ f x v + fderiv ℝ χ x v • f x := by
  have he := (hχ.hasFDerivAt.smul hf.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => χ y • f y) x=_ at he
  rw [he]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply]

theorem actual_cutoff_second_fderiv {χ : Configuration 2 → ℝ}
    {f : Configuration 2 → ℂ} {x : Configuration 2}
    (hχ : ContDiffAt ℝ 2 χ x) (hf : ContDiffAt ℝ 2 f x)
    (v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => χ z • f z) y v) x w =
      χ x • fderiv ℝ (fun y => fderiv ℝ f y v) x w+
      fderiv ℝ χ x w • fderiv ℝ f x v+
      fderiv ℝ χ x v • fderiv ℝ f x w+
      fderiv ℝ (fun y => fderiv ℝ χ y v) x w • f x := by
  have he : (fun y => fderiv ℝ (fun z => χ z • f z) y v)=ᶠ[𝓝 x]
      (fun y => χ y • fderiv ℝ f y v+fderiv ℝ χ y v • f y) := by
    filter_upwards [hχ.eventually (by norm_num),hf.eventually (by norm_num)] with y hy hz
    exact actual_cutoff_first_fderiv (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num)) v
  rw [he.fderiv_eq]
  have hχ' := (hχ.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hf' := (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hc := hχ'.clm_apply (differentiableAt_const v)
  have hd := hf'.clm_apply (differentiableAt_const v)
  change DifferentiableAt ℝ (fun y => fderiv ℝ χ y v) x at hc
  change DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x at hd
  have headd := (((hχ.differentiableAt (by norm_num)).smul hd).hasFDerivAt.add
    (hc.smul (hf.differentiableAt (by norm_num))).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => χ y • fderiv ℝ f y v+fderiv ℝ χ y v • f y) x=_ at headd
  rw [headd]
  simp only [add_apply]
  change fderiv ℝ (fun y => χ y • fderiv ℝ f y v) x w +
    fderiv ℝ (fun y => fderiv ℝ χ y v • f y) x w = _
  rw [actual_cutoff_first_fderiv (hχ.differentiableAt (by norm_num)) hd,
    actual_cutoff_first_fderiv hc (hf.differentiableAt (by norm_num))]
  abel

def physicalCutoffDistanceValue (χ : Configuration 2 → ℝ) (g : (Fin 3 → ℝ) → ℂ)
    (x : Configuration 2) : ℂ := χ x • g (physicalDistanceTriple x)

def physicalCutoffDistanceFirst (χ : Configuration 2 → ℝ) (g : (Fin 3 → ℝ) → ℂ)
    (x v : Configuration 2) : ℂ :=
  χ x • physicalDistanceCompositionFirst g x v+
    fderiv ℝ χ x v • g (physicalDistanceTriple x)

def physicalCutoffDistanceSecond (χ : Configuration 2 → ℝ) (g : (Fin 3 → ℝ) → ℂ)
    (x v w : Configuration 2) : ℂ :=
  χ x • physicalDistanceCompositionSecond g x v w+
    fderiv ℝ χ x w • physicalDistanceCompositionFirst g x v+
    fderiv ℝ χ x v • physicalDistanceCompositionFirst g x w+
    fderiv ℝ (fun y => fderiv ℝ χ y v) x w • g (physicalDistanceTriple x)

theorem physical_cutoff_distance_first {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {x : Configuration 2}
    (hχ : DifferentiableAt ℝ χ x) (hg : DifferentiableAt ℝ g (physicalDistanceTriple x))
    (hx : collisionFree x) (v : Configuration 2) :
    fderiv ℝ (physicalCutoffDistanceValue χ g) x v=physicalCutoffDistanceFirst χ g x v := by
  change fderiv ℝ (fun y => χ y • (g∘physicalDistanceTriple) y) x v=_
  rw [actual_cutoff_first_fderiv hχ
    (hg.comp x (physical_distance_triple_hasFDerivAt hx).differentiableAt),
    physical_distance_composition_first hx hg]
  rfl

theorem physical_cutoff_distance_second {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {x : Configuration 2}
    (hχ : ContDiffAt ℝ 2 χ x) (hg : ContDiffAt ℝ 2 g (physicalDistanceTriple x))
    (hx : collisionFree x) (v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (physicalCutoffDistanceValue χ g) y v) x w=
      physicalCutoffDistanceSecond χ g x v w := by
  have hd := (physical_distance_triple_contDiffAt hx).of_le (by simp : (2:WithTop ℕ∞)≤∞)
  change fderiv ℝ (fun y => fderiv ℝ (fun z => χ z • (g∘physicalDistanceTriple) z) y v) x w=_
  rw [actual_cutoff_second_fderiv hχ (hg.comp x hd),
    physical_distance_composition_second hx hg,
    physical_distance_composition_first hx (hg.differentiableAt (by norm_num)),
    physical_distance_composition_first hx (hg.differentiableAt (by norm_num))]
  rfl


def regularizedDistanceCompositionFirst (g : (Fin 3 → ℝ) → ℂ)
    (δ : ℝ) (x v : Configuration 2) : ℂ :=
  fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)
    (regularizedPhysicalDistanceGradient δ x v)

def regularizedDistanceCompositionSecond (g : (Fin 3 → ℝ) → ℂ)
    (δ : ℝ) (x v w : Configuration 2) : ℂ :=
  fderiv ℝ (fderiv ℝ g) (regularizedPhysicalDistanceTriple δ x)
    (regularizedPhysicalDistanceGradient δ x w) (regularizedPhysicalDistanceGradient δ x v)+
  fderiv ℝ g (regularizedPhysicalDistanceTriple δ x)
    (regularizedPhysicalDistanceHessian δ x v w)

def regularizedCutoffDistanceValue (χ : Configuration 2 → ℝ) (g : (Fin 3 → ℝ) → ℂ)
    (δ : ℝ) (x : Configuration 2) : ℂ := χ x • g (regularizedPhysicalDistanceTriple δ x)

def regularizedCutoffDistanceFirst (χ : Configuration 2 → ℝ) (g : (Fin 3 → ℝ) → ℂ)
    (δ : ℝ) (x v : Configuration 2) : ℂ :=
  χ x • regularizedDistanceCompositionFirst g δ x v+
    fderiv ℝ χ x v • g (regularizedPhysicalDistanceTriple δ x)

def regularizedCutoffDistanceSecond (χ : Configuration 2 → ℝ) (g : (Fin 3 → ℝ) → ℂ)
    (δ : ℝ) (x v w : Configuration 2) : ℂ :=
  χ x • regularizedDistanceCompositionSecond g δ x v w+
    fderiv ℝ χ x w • regularizedDistanceCompositionFirst g δ x v+
    fderiv ℝ χ x v • regularizedDistanceCompositionFirst g δ x w+
    fderiv ℝ (fun y => fderiv ℝ χ y v) x w • g (regularizedPhysicalDistanceTriple δ x)

theorem regularized_distance_composition_first {g : (Fin 3 → ℝ) → ℂ}
    {δ : ℝ} (hδ : 0<δ) (hg : ContDiff ℝ ∞ g) (x v : Configuration 2) :
    fderiv ℝ (g∘regularizedPhysicalDistanceTriple δ) x v=
      regularizedDistanceCompositionFirst g δ x v := by
  rw [fderiv_comp x (hg.differentiable (by simp) _)
    ((regularized_physical_distance_contDiff hδ).differentiable (by simp) x),
    ContinuousLinearMap.comp_apply,regularized_physical_distance_fderiv hδ]
  rfl

theorem regularized_distance_composition_second {g : (Fin 3 → ℝ) → ℂ}
    {δ : ℝ} (hδ : 0<δ) (hg : ContDiff ℝ ∞ g) (x v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (g∘regularizedPhysicalDistanceTriple δ) y v) x w=
      regularizedDistanceCompositionSecond g δ x v w := by
  rw [actual_composition_mixed_fderiv
    ((regularized_physical_distance_contDiff hδ).contDiffAt.of_le (by simp))
    (hg.contDiffAt.of_le (by simp)), regularized_physical_distance_fderiv hδ,
    regularized_physical_distance_fderiv hδ,regularized_physical_distance_mixed_fderiv hδ]
  rfl

theorem regularized_cutoff_distance_first {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {δ : ℝ} (hδ : 0<δ)
    (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) (x v : Configuration 2) :
    fderiv ℝ (regularizedCutoffDistanceValue χ g δ) x v=
      regularizedCutoffDistanceFirst χ g δ x v := by
  have hh := hg.comp (regularized_physical_distance_contDiff hδ)
  change fderiv ℝ (fun y => χ y • (g∘regularizedPhysicalDistanceTriple δ) y) x v=_
  rw [actual_cutoff_first_fderiv (hχ.differentiable (by simp) x)
    (hh.differentiable (by simp) x), regularized_distance_composition_first hδ hg]
  rfl

theorem regularized_cutoff_distance_second {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} {δ : ℝ} (hδ : 0<δ)
    (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) (x v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (regularizedCutoffDistanceValue χ g δ) y v) x w=
      regularizedCutoffDistanceSecond χ g δ x v w := by
  have hh := hg.comp (regularized_physical_distance_contDiff hδ)
  change fderiv ℝ (fun y => fderiv ℝ (fun z => χ z • (g∘regularizedPhysicalDistanceTriple δ) z) y v) x w=_
  rw [actual_cutoff_second_fderiv (hχ.contDiffAt.of_le (by simp))
    (hh.contDiffAt.of_le (by simp)),regularized_distance_composition_second hδ hg,
    regularized_distance_composition_first hδ hg,regularized_distance_composition_first hδ hg]
  rfl

theorem actual_clm_application_tendsto
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : ℕ→E→L[ℝ]F} {v : ℕ→E} {L0 : E→L[ℝ]F} {v0 : E}
    (hL : Tendsto L atTop (𝓝 L0)) (hv : Tendsto v atTop (𝓝 v0)) :
    Tendsto (fun n => L n (v n)) atTop (𝓝 (L0 v0)) :=
  (isBoundedBilinearMap_apply.continuous.tendsto (L0,v0)).comp (hL.prodMk_nhds hv)

theorem regularized_cutoff_distance_value_tendsto {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} (hg : Continuous g)
    {δ : ℕ→ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (x : Configuration 2) :
    Tendsto (fun n => regularizedCutoffDistanceValue χ g (δ n) x) atTop
      (𝓝 (physicalCutoffDistanceValue χ g x)) :=
  tendsto_const_nhds.smul ((hg.tendsto _).comp (regularized_physical_distance_tendsto hδ x))

theorem regularized_cutoff_distance_first_tendsto {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    {δ : ℕ→ℝ} (hp : ∀n,0<δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration 2} (hx : collisionFree x) (v : Configuration 2) :
    Tendsto (fun n => regularizedCutoffDistanceFirst χ g (δ n) x v) atTop
      (𝓝 (physicalCutoffDistanceFirst χ g x v)) := by
  have hq := regularized_physical_distance_tendsto hδ x
  have hD := ((hg.fderiv_right (m:=∞) (by simp)).continuous.tendsto _).comp hq
  have hF := actual_clm_application_tendsto hD
    (regularized_physical_distance_gradient_tendsto hp hδ hx v)
  exact (tendsto_const_nhds.smul hF).add
    (tendsto_const_nhds.smul ((hg.continuous.tendsto _).comp hq))

theorem regularized_cutoff_distance_second_tendsto {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    {δ : ℕ→ℝ} (hp : ∀n,0<δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration 2} (hx : collisionFree x) (v w : Configuration 2) :
    Tendsto (fun n => regularizedCutoffDistanceSecond χ g (δ n) x v w) atTop
      (𝓝 (physicalCutoffDistanceSecond χ g x v w)) := by
  have hq := regularized_physical_distance_tendsto hδ x
  have hd := hg.fderiv_right (by simp : (∞:WithTop ℕ∞)+1≤∞)
  have hD := (hd.continuous.tendsto _).comp hq
  have hDD := ((hd.fderiv_right (m:=∞) (by simp)).continuous.tendsto _).comp hq
  have hv := regularized_physical_distance_gradient_tendsto hp hδ hx v
  have hw := regularized_physical_distance_gradient_tendsto hp hδ hx w
  have hF := actual_clm_application_tendsto hD hv
  have hG := actual_clm_application_tendsto hD hw
  have h2 := (actual_clm_application_tendsto (actual_clm_application_tendsto hDD hw) hv).add
    (actual_clm_application_tendsto hD (regularized_physical_distance_hessian_tendsto hp hδ hx v w))
  exact (((tendsto_const_nhds.smul h2).add (tendsto_const_nhds.smul hF)).add
    (tendsto_const_nhds.smul hG)).add
    (tendsto_const_nhds.smul ((hg.continuous.tendsto _).comp hq))

#print axioms regularized_cutoff_distance_second_tendsto
#print axioms physical_cutoff_distance_second
end ManyBody.S8