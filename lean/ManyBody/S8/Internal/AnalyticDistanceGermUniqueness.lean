import ContinuumFoundation_v1
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic
/-! Uniqueness of the collision-centered analytic distance decomposition.

The two actual three-vector variables are the selected physical separation X
and spectator coordinate T. If two real analytic pairs represent the same
function as A(X,T) + norm(X) * B(X,T) near X=0, their real analytic germs agree
separately. Signed line restrictions derive both A+t*B and A-t*B identities;
real analytic uniqueness supplies the collision value as well.

This module is a uniqueness bridge. It does not assume or prove that a
particular physical Coulomb state admits such a decomposition, and it does
not provide global chart coverage or an approximation algorithm.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace ManyBody.S8
open TheoremT.Continuum

theorem analytic_abs_linear_zero_unique
    {a b : ℝ → ℂ}
    (ha : AnalyticOnNhd ℝ a (Ioo (-2 : ℝ) 2))
    (hb : AnalyticOnNhd ℝ b (Ioo (-2 : ℝ) 2))
    (heq : ∀ t ∈ Ioo (-2 : ℝ) 2, a t + |t| • b t = 0) :
    ∀ t ∈ Ioo (-2 : ℝ) 2, a t = 0 ∧ b t = 0 := by
  have hplus : AnalyticOnNhd ℝ (fun t => a t + t • b t) (Ioo (-2 : ℝ) 2) := by
    intro t ht
    exact (ha t ht).add (analyticAt_id.smul (hb t ht))
  have hminus : AnalyticOnNhd ℝ (fun t => a t - t • b t) (Ioo (-2 : ℝ) 2) := by
    intro t ht
    exact (ha t ht).sub (analyticAt_id.smul (hb t ht))
  have hpnear : (fun t => a t + t • b t) =ᶠ[𝓝 (1 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (1:ℝ) ∈ Ioo (0:ℝ) 2)] with t ht
    simpa only [Pi.zero_apply,abs_of_pos ht.1] using heq t ⟨by linarith [ht.1],ht.2⟩
  have hmnear : (fun t => a t - t • b t) =ᶠ[𝓝 (-1 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (-1:ℝ) ∈ Ioo (-2:ℝ) 0)] with t ht
    have hh := heq t ⟨ht.1,by linarith [ht.2]⟩
    simpa only [Pi.zero_apply,abs_of_neg ht.2,neg_smul,← sub_eq_add_neg] using hh
  have hp := hplus.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    (by norm_num : (1:ℝ) ∈ Ioo (-2:ℝ) 2) hpnear
  have hm := hminus.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    (by norm_num : (-1:ℝ) ∈ Ioo (-2:ℝ) 2) hmnear
  have hbne (t : ℝ) (ht : t ∈ Ioo (-2:ℝ) 2) (htne : t ≠ 0) : b t = 0 := by
    have hh : (2*t) • b t = 0 := by
      calc
        _ = (a t+t • b t)-(a t-t • b t) := by module
        _ = 0 := by
          have hpt : a t+t • b t=0 := hp ht
          have hmt : a t-t • b t=0 := hm ht
          rw [hpt,hmt,sub_self]
    exact (smul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) htne)
  have hbnear : b =ᶠ[𝓝 (1:ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (1:ℝ) ∈ Ioo (0:ℝ) 2)] with t ht
    exact hbne t ⟨by linarith [ht.1],ht.2⟩ (ne_of_gt ht.1)
  have hbzero := hb.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    (by norm_num : (1:ℝ) ∈ Ioo (-2:ℝ) 2) hbnear
  intro t ht
  have hb0 := hbzero ht
  refine ⟨?_,hb0⟩
  simpa only [hb0,smul_zero,add_zero,Pi.zero_apply] using hp ht

#print axioms analytic_abs_linear_zero_unique

def collisionProductNeighborhood (r s : ℝ) (t0 : Position) : Set (Position × Position) :=
  {p | ‖p.1‖ < r ∧ ‖p.2-t0‖ < s}

theorem analytic_distance_zero_unique
    {a b : Position × Position → ℂ} {r s : ℝ} {t0 : Position} (hr : 0 < r)
    (ha : AnalyticOnNhd ℝ a (collisionProductNeighborhood r s t0))
    (hb : AnalyticOnNhd ℝ b (collisionProductNeighborhood r s t0))
    (heq : ∀ p ∈ collisionProductNeighborhood r s t0, a p+‖p.1‖ • b p=0) :
    ∀ X T : Position, ‖X‖ < r/2 → ‖T-t0‖ < s →
      a (X,T)=0 ∧ b (X,T)=0 := by
  have hline (X T : Position) (hX : ‖X‖ < r/2) (hT : ‖T-t0‖ < s) :
      ∀ t ∈ Ioo (-2:ℝ) 2,
        a (t • X,T)=0 ∧ ‖X‖ • b (t • X,T)=0 := by
    have hmem (t : ℝ) (ht : t ∈ Ioo (-2:ℝ) 2) :
        (t • X,T) ∈ collisionProductNeighborhood r s t0 := by
      refine ⟨?_,hT⟩
      rw [norm_smul,Real.norm_eq_abs]
      have hlt : |t| < 2 := abs_lt.mpr ht
      have hh := mul_le_mul_of_nonneg_right hlt.le (norm_nonneg X)
      nlinarith
    have hanline (t : ℝ) : AnalyticAt ℝ (fun u : ℝ => (u • X,T)) t :=
      (analyticAt_id.smul analyticAt_const).prod analyticAt_const
    have haline : AnalyticOnNhd ℝ (fun t : ℝ => a (t • X,T)) (Ioo (-2:ℝ) 2) := by
      intro t ht
      exact AnalyticAt.comp (f := fun u : ℝ => (u • X,T)) (g := a) (x := t) (ha _ (hmem t ht)) (hanline t)
    have hbline : AnalyticOnNhd ℝ (fun t : ℝ => ‖X‖ • b (t • X,T)) (Ioo (-2:ℝ) 2) := by
      intro t ht
      exact (AnalyticAt.comp (f := fun u : ℝ => (u • X,T)) (g := b) (x := t) (hb _ (hmem t ht)) (hanline t)).const_smul (c := ‖X‖)
    apply analytic_abs_linear_zero_unique haline hbline
    intro t ht
    have hh := heq (t • X,T) (hmem t ht)
    simpa only [norm_smul,Real.norm_eq_abs,smul_smul] using hh
  intro X T hX hT
  have hbzero : b (X,T)=0 := by
    by_cases hX0 : X=0
    · let v : Position := PiLp.single 2 (0:Fin 3) (1:ℝ)
      have hv : ‖v‖=1 := by simp only [v,PiLp.norm_single,norm_one]
      let w : Position := (r/4) • v
      have hw : ‖w‖=r/4 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),hv,mul_one]
      have hwlt : ‖w‖ < r/2 := by rw [hw]; linarith
      have hh := (hline w T hwlt hT 0 (by norm_num)).2
      rw [zero_smul] at hh
      rw [hX0]
      exact (smul_eq_zero.mp hh).resolve_left (by rw [hw]; positivity)
    · have hh := (hline X T hX hT 1 (by norm_num)).2
      rw [one_smul] at hh
      exact (smul_eq_zero.mp hh).resolve_left (norm_ne_zero_iff.mpr hX0)
  refine ⟨?_,hbzero⟩
  have hh := heq (X,T) ⟨by linarith,hT⟩
  simpa only [hbzero,smul_zero,add_zero] using hh

theorem analytic_distance_decomposition_unique
    {a₁ a₂ b₁ b₂ : Position × Position → ℂ} {r s : ℝ} {t0 : Position} (hr : 0 < r)
    (ha₁ : AnalyticOnNhd ℝ a₁ (collisionProductNeighborhood r s t0))
    (ha₂ : AnalyticOnNhd ℝ a₂ (collisionProductNeighborhood r s t0))
    (hb₁ : AnalyticOnNhd ℝ b₁ (collisionProductNeighborhood r s t0))
    (hb₂ : AnalyticOnNhd ℝ b₂ (collisionProductNeighborhood r s t0))
    (heq : ∀ p ∈ collisionProductNeighborhood r s t0,
      a₁ p+‖p.1‖ • b₁ p=a₂ p+‖p.1‖ • b₂ p) :
    ∀ X T : Position, ‖X‖ < r/2 → ‖T-t0‖ < s →
      a₁ (X,T)=a₂ (X,T) ∧ b₁ (X,T)=b₂ (X,T) := by
  have hh := analytic_distance_zero_unique hr (ha₁.sub ha₂) (hb₁.sub hb₂)
    (fun p hp => by
      have he := heq p hp
      change a₁ p-a₂ p+‖p.1‖ • (b₁ p-b₂ p)=0
      calc
        _ = (a₁ p+‖p.1‖ • b₁ p)-(a₂ p+‖p.1‖ • b₂ p) := by module
        _ = 0 := sub_eq_zero.mpr he)
  intro X T hX hT
  obtain ⟨ha,hb⟩ := hh X T hX hT
  exact ⟨sub_eq_zero.mp ha,sub_eq_zero.mp hb⟩

#print axioms analytic_distance_zero_unique
#print axioms analytic_distance_decomposition_unique

theorem analytic_distance_decomposition_germ_unique
    {a₁ a₂ b₁ b₂ : Position × Position → ℂ} (t0 : Position)
    (ha₁ : AnalyticAt ℝ a₁ (0,t0)) (ha₂ : AnalyticAt ℝ a₂ (0,t0))
    (hb₁ : AnalyticAt ℝ b₁ (0,t0)) (hb₂ : AnalyticAt ℝ b₂ (0,t0))
    (heq : (fun p => a₁ p+‖p.1‖ • b₁ p) =ᶠ[𝓝 ((0:Position),t0)]
      (fun p => a₂ p+‖p.1‖ • b₂ p)) :
    (a₁ =ᶠ[𝓝 ((0:Position),t0)] a₂) ∧ (b₁ =ᶠ[𝓝 ((0:Position),t0)] b₂) := by
  have hevent : ∀ᶠ p in 𝓝 ((0:Position),t0),
      AnalyticAt ℝ a₁ p ∧ AnalyticAt ℝ a₂ p ∧
      AnalyticAt ℝ b₁ p ∧ AnalyticAt ℝ b₂ p ∧
      a₁ p+‖p.1‖ • b₁ p=a₂ p+‖p.1‖ • b₂ p := by
    filter_upwards [ha₁.eventually_analyticAt,ha₂.eventually_analyticAt,
      hb₁.eventually_analyticAt,hb₂.eventually_analyticAt,heq] with p h1 h2 h3 h4 he
    exact ⟨h1,h2,h3,h4,he⟩
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  have hmem (p : Position × Position) (hp : p ∈ collisionProductNeighborhood r r t0) :
      dist p ((0:Position),t0) < r := by
    rw [Prod.dist_eq,dist_zero_right,dist_eq_norm]
    exact max_lt hp.1 hp.2
  have huniq := analytic_distance_decomposition_unique hr
    (fun p hp => (hball (hmem p hp)).1)
    (fun p hp => (hball (hmem p hp)).2.1)
    (fun p hp => (hball (hmem p hp)).2.2.1)
    (fun p hp => (hball (hmem p hp)).2.2.2.1)
    (fun p hp => (hball (hmem p hp)).2.2.2.2)
  have hopen : IsOpen (collisionProductNeighborhood (r/2) r t0) :=
    (isOpen_lt continuous_fst.norm continuous_const).inter
      (isOpen_lt (continuous_snd.sub continuous_const).norm continuous_const)
  have hcenter : ((0:Position),t0) ∈ collisionProductNeighborhood (r/2) r t0 := by
    constructor
    · simpa only [norm_zero] using (half_pos hr)
    · simpa only [sub_self,norm_zero] using hr
  have hh : ∀ᶠ p in 𝓝 ((0:Position),t0), a₁ p=a₂ p ∧ b₁ p=b₂ p := by
    filter_upwards [hopen.mem_nhds hcenter] with p hp
    exact huniq p.1 p.2 hp.1 hp.2
  exact ⟨hh.mono fun _ h => h.1,hh.mono fun _ h => h.2⟩

#print axioms analytic_distance_decomposition_germ_unique
end ManyBody.S8