import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
/-! A real open slice determines the germ of a holomorphic distance function.

The real three-distance embedding is the actual coordinatewise complex cast,
with its exact norm. One-complex-variable analytic uniqueness first extends
equality along each real direction to its complex line. A second complex
line separates the real and imaginary vector parts of an arbitrary nearby
point. This proves complex germ equality from equality on a genuine real
open ball, without treating the real plane as a complex open neighborhood.

The declarations here are generic uniqueness bridges. Physical consumers
must derive real slice equality from their actual reconstruction identity;
no Coulomb or chart applicability is asserted by this helper alone.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ManyBody.S8

def ambientRealCastLinear : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℂ) where
  toFun p := fun j => (p j : ℂ)
  map_add' p q := by ext j; simp
  map_smul' r p := by ext j; simp [Complex.real_smul]

def ambientRealCast : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℂ) :=
  ambientRealCastLinear.toContinuousLinearMap

@[simp] theorem ambientRealCast_apply (p : Fin 3 → ℝ) (j : Fin 3) :
    ambientRealCast p j=(p j:ℂ) := rfl

theorem ambientRealCast_norm (p : Fin 3 → ℝ) : ‖ambientRealCast p‖=‖p‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    simpa only [ambientRealCast_apply,Complex.norm_real] using norm_le_pi_norm p j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    simpa only [ambientRealCast_apply,Complex.norm_real] using norm_le_pi_norm (ambientRealCast p) j

theorem complex_real_interval_identity {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 2)) (hg : AnalyticOnNhd ℂ g (ball 0 2))
    (heq : ∀ t : ℝ, |t|<2 → f (t:ℂ)=g (t:ℂ)) : EqOn f g (ball 0 2) := by
  apply hf.eqOn_of_preconnected_of_frequently_eq (z₀ := (0:ℂ)) hg (convex_ball _ _).isPreconnected
    (by simp)
  by_contra hfreq
  have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), f z≠g z := not_frequently.mp hfreq
  have hh := eventually_nhdsWithin_iff.mp hne
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hh
  let t : ℝ := min r 1/2
  have ht : 0<t := by dsimp [t]; positivity
  have htr : t<r := by have hh := min_le_left r 1; dsimp [t]; linarith
  have ht2 : |t|<2 := by rw [abs_of_pos ht]; have hh := min_le_right r 1; dsimp [t]; linarith
  have htc : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  have hd : dist (t:ℂ) 0<r := by
    rw [dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]; exact htr
  exact hball hd htc (heq t ht2)

theorem complex_real_ball_identity {f g : (Fin 3 → ℂ) → ℂ}
    {a : Fin 3 → ℝ} {r : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (ball (ambientRealCast a) r))
    (hg : AnalyticOnNhd ℂ g (ball (ambientRealCast a) r))
    (heq : ∀ p : Fin 3 → ℝ, ‖p-a‖<r → f (ambientRealCast p)=g (ambientRealCast p)) :
    EqOn f g (ball (ambientRealCast a) (r/16)) := by
  have hfirst (b w : Fin 3 → ℝ) (hb : ‖b-a‖<r/4) (hw : ‖w‖<r/4) :
      f (ambientRealCast b+Complex.I • ambientRealCast w)=
      g (ambientRealCast b+Complex.I • ambientRealCast w) := by
    have hmem (z : ℂ) (hz : z∈ball 0 2) :
        ambientRealCast b+z • ambientRealCast w∈ball (ambientRealCast a) r := by
      rw [mem_ball,dist_eq_norm]
      have htri := norm_add_le (ambientRealCast (b-a)) (z • ambientRealCast w)
      have hz' : ‖z‖<2 := by simpa only [mem_ball,dist_zero_right] using hz
      rw [norm_smul,ambientRealCast_norm,ambientRealCast_norm] at htri
      have hh : ‖z‖*‖w‖≤2*‖w‖ := mul_le_mul_of_nonneg_right hz'.le (norm_nonneg w)
      have he : ambientRealCast b+z • ambientRealCast w-ambientRealCast a=
          ambientRealCast (b-a)+z • ambientRealCast w := by rw [map_sub]; abel
      rw [he]
      linarith
    have hline (z : ℂ) : AnalyticAt ℂ (fun z => ambientRealCast b+z • ambientRealCast w) z :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hEq := complex_real_interval_identity
      (fun z hz => AnalyticAt.comp (g := f) (f := fun z => ambientRealCast b+z • ambientRealCast w) (hf _ (hmem z hz)) (hline z))
      (fun z hz => AnalyticAt.comp (g := g) (f := fun z => ambientRealCast b+z • ambientRealCast w) (hg _ (hmem z hz)) (hline z)) ?_
    · simpa using hEq (by simp : Complex.I∈ball (0:ℂ) 2)
    · intro t ht
      have htc : (t:ℂ)∈ball (0:ℂ) 2 := by simpa [Complex.norm_real] using ht
      have hm := hmem (t:ℂ) htc
      have hmap : ambientRealCast (b+t • w)=ambientRealCast b+(t:ℂ) • ambientRealCast w := by
        rw [map_add,map_smul]; rfl
      have hb' : ‖b+t • w-a‖<r := by
        rw [←ambientRealCast_norm,map_sub,hmap]
        simpa only [mem_ball,dist_eq_norm] using hm
      simpa only [hmap,Function.comp_apply] using heq (b+t • w) hb'
  intro q hq
  have hqnorm : ‖q-ambientRealCast a‖<r/16 := by simpa only [mem_ball,dist_eq_norm] using hq
  let v : Fin 3 → ℝ := fun j => (q j-(a j:ℂ)).re
  let w : Fin 3 → ℝ := fun j => (q j-(a j:ℂ)).im
  have hv : ‖v‖≤‖q-ambientRealCast a‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm (q-ambientRealCast a) j)
  have hw : ‖w‖≤‖q-ambientRealCast a‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm (q-ambientRealCast a) j)
  have hmem (z : ℂ) (hz : z∈ball 0 2) :
      ambientRealCast a+z • ambientRealCast v+Complex.I • ambientRealCast w∈
        ball (ambientRealCast a) r := by
    rw [mem_ball,dist_eq_norm]
    have he : ambientRealCast a+z • ambientRealCast v+Complex.I • ambientRealCast w-
        ambientRealCast a=z • ambientRealCast v+Complex.I • ambientRealCast w := by abel
    rw [he]
    have htri := norm_add_le (z • ambientRealCast v) (Complex.I • ambientRealCast w)
    rw [norm_smul,norm_smul,ambientRealCast_norm,ambientRealCast_norm,Complex.norm_I,one_mul] at htri
    have hz' : ‖z‖<2 := by simpa only [mem_ball,dist_zero_right] using hz
    have hh : ‖z‖*‖v‖≤2*‖v‖ := mul_le_mul_of_nonneg_right hz'.le (norm_nonneg v)
    linarith
  have hline (z : ℂ) : AnalyticAt ℂ
      (fun z => ambientRealCast a+z • ambientRealCast v+Complex.I • ambientRealCast w) z :=
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const)).add analyticAt_const
  have hEq := complex_real_interval_identity
    (fun z hz => AnalyticAt.comp (g := f) (f := fun z => ambientRealCast a+z • ambientRealCast v+Complex.I • ambientRealCast w) (hf _ (hmem z hz)) (hline z))
    (fun z hz => AnalyticAt.comp (g := g) (f := fun z => ambientRealCast a+z • ambientRealCast v+Complex.I • ambientRealCast w) (hg _ (hmem z hz)) (hline z)) ?_
  · have he : ambientRealCast a+ambientRealCast v+Complex.I • ambientRealCast w=q := by
      ext j
      have hh := Complex.re_add_im (q j-(a j:ℂ))
      dsimp [v,w]
      rw [mul_comm Complex.I]
      linear_combination hh
    simpa only [Function.comp_apply,one_smul,he] using hEq (by simp : (1:ℂ)∈ball 0 2)
  · intro t ht
    have hb : ‖a+t • v-a‖<r/4 := by
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
      have hh : |t| *‖v‖≤2*‖v‖ := mul_le_mul_of_nonneg_right ht.le (norm_nonneg v)
      linarith
    have hw' : ‖w‖<r/4 := by linarith
    have hh := hfirst (a+t • v) w hb hw'
    have hmap : ambientRealCast (a+t • v)=ambientRealCast a+(t:ℂ) • ambientRealCast v := by
      rw [map_add,map_smul]; rfl
    simpa only [hmap,Function.comp_apply] using hh

#print axioms complex_real_interval_identity
#print axioms complex_real_ball_identity

theorem complex_real_germ_identity {f g : (Fin 3 → ℂ) → ℂ} (a : Fin 3 → ℝ)
    (hf : AnalyticAt ℂ f (ambientRealCast a)) (hg : AnalyticAt ℂ g (ambientRealCast a))
    (heq : (fun p => f (ambientRealCast p)) =ᶠ[𝓝 a] (fun p => g (ambientRealCast p))) :
    f =ᶠ[𝓝 (ambientRealCast a)] g := by
  obtain ⟨rA,hrA,hA⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  obtain ⟨rE,hrE,hE⟩ := Metric.eventually_nhds_iff.mp heq
  let r : ℝ := min rA rE
  have hr : 0<r := lt_min hrA hrE
  have hf' : AnalyticOnNhd ℂ f (ball (ambientRealCast a) r) :=
    fun _ hp => (hA (hp.trans_le (min_le_left _ _))).1
  have hg' : AnalyticOnNhd ℂ g (ball (ambientRealCast a) r) :=
    fun _ hp => (hA (hp.trans_le (min_le_left _ _))).2
  have heq' (p : Fin 3 → ℝ) (hp : ‖p-a‖<r) :
      f (ambientRealCast p)=g (ambientRealCast p) :=
    hE (by rw [dist_eq_norm]; exact hp.trans_le (min_le_right _ _))
  have hh := complex_real_ball_identity hr hf' hg' heq'
  filter_upwards [ball_mem_nhds (ambientRealCast a) (by positivity : 0<r/16)] with q hq
  exact hh hq

#print axioms complex_real_germ_identity
end ManyBody.S8