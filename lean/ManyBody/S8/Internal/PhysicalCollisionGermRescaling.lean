import ManyBody.S8.Internal.AnalyticDistanceGermUniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic
/-! Exact return from normalized physical differences to the original germ.

For each positive scale, the original A term is u(0) + epsilon times
A_scaled at inverse-scaled physical coordinates. The original B term is
B_scaled at those same coordinates; the norm factor absorbs the scale.
The genuine real analytic identity is transported through the actual scalar
coordinate map, and collision-germ uniqueness proves separate compatibility
across scales at the same original physical collision point.

This algebraic/analytic bridge takes the displayed normalized physical
identity as a premise. Concrete Coulomb graph consumers must derive that
identity from the unchanged physical operator and actual coordinate maps.
-/
noncomputable section
open Filter
open scoped Topology
namespace ManyBody.S8
open TheoremT.Continuum

def physicalRescaledCollisionA (ε : ℝ) (u0 : ℂ)
    (a : Position × Position → ℂ) (p : Position × Position) : ℂ :=
  u0+(ε:ℂ)*a (ε⁻¹ • p)

def physicalRescaledCollisionB (ε : ℝ)
    (b : Position × Position → ℂ) (p : Position × Position) : ℂ :=
  b (ε⁻¹ • p)

theorem physical_collision_germ_rescale
    {a b v : Position × Position → ℂ} {ε : ℝ} {tStar : Position}
    (hε : 0<ε) (ha : AnalyticAt ℝ a (0,tStar))
    (hb : AnalyticAt ℝ b (0,tStar))
    (heq : (fun p => a p+‖p.1‖ • b p) =ᶠ[𝓝 ((0:Position),tStar)]
      (fun p => (v (ε • p)-v 0)/(ε:ℂ))) :
    AnalyticAt ℝ (physicalRescaledCollisionA ε (v 0) a) (0,ε • tStar) ∧
    AnalyticAt ℝ (physicalRescaledCollisionB ε b) (0,ε • tStar) ∧
    (fun p => physicalRescaledCollisionA ε (v 0) a p+
      ‖p.1‖ • physicalRescaledCollisionB ε b p)
      =ᶠ[𝓝 ((0:Position),ε • tStar)] v := by
  have hcenter : ε⁻¹ • ((0:Position),ε • tStar)=((0:Position),tStar) := by
    simp [smul_smul,hε.ne']
  have hs : AnalyticAt ℝ (fun p : Position × Position => ε⁻¹ • p)
      ((0:Position),ε • tStar) := by
    have hcst : AnalyticAt ℝ (fun _ : Position × Position => ε⁻¹)
        ((0:Position),ε • tStar) := analyticAt_const
    exact hcst.smul analyticAt_id
  have ha' : AnalyticAt ℝ (fun p : Position × Position => a (ε⁻¹ • p))
      ((0:Position),ε • tStar) := by
    apply AnalyticAt.comp (f := fun p : Position × Position => ε⁻¹ • p) (g := a) _ hs
    simpa only [hcenter] using ha
  have hb' : AnalyticAt ℝ (fun p : Position × Position => b (ε⁻¹ • p))
      ((0:Position),ε • tStar) := by
    apply AnalyticAt.comp (f := fun p : Position × Position => ε⁻¹ • p) (g := b) _ hs
    simpa only [hcenter] using hb
  refine ⟨analyticAt_const.add (analyticAt_const.mul ha'),hb',?_⟩
  have ht : Tendsto (fun p : Position × Position => ε⁻¹ • p)
      (𝓝 ((0:Position),ε • tStar)) (𝓝 ((0:Position),tStar)) := by
    simpa only [ContinuousAt,hcenter] using hs.continuousAt
  filter_upwards [heq.comp_tendsto ht] with p hp
  dsimp only [Function.comp_apply] at hp
  have hcancel : ε • (ε⁻¹ • p)=p := by simp [smul_smul,hε.ne']
  have hnorm : ‖(ε⁻¹ • p).1‖=ε⁻¹*‖p.1‖ := by
    change ‖ε⁻¹ • p.1‖=ε⁻¹*‖p.1‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hε)]
  rw [hcancel,hnorm,Complex.real_smul] at hp
  have hc : (ε:ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  change v 0+(ε:ℂ)*a (ε⁻¹ • p)+(‖p.1‖:ℂ)*b (ε⁻¹ • p)=v p
  have hh := (eq_div_iff hc).mp hp
  push_cast at hh
  field_simp [hc] at hh
  simp only [one_div] at hh
  linear_combination hh

#print axioms physical_collision_germ_rescale

theorem physical_rescaled_collision_germ_unique
    {a₀ b₀ a₁ b₁ v : Position × Position → ℂ}
    {ε₀ ε₁ : ℝ} {t₀ t₁ tStar : Position}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁)
    (hpoint₀ : ε₀ • t₀=tStar) (hpoint₁ : ε₁ • t₁=tStar)
    (ha₀ : AnalyticAt ℝ a₀ (0,t₀)) (hb₀ : AnalyticAt ℝ b₀ (0,t₀))
    (ha₁ : AnalyticAt ℝ a₁ (0,t₁)) (hb₁ : AnalyticAt ℝ b₁ (0,t₁))
    (heq₀ : (fun p => a₀ p+‖p.1‖ • b₀ p) =ᶠ[𝓝 ((0:Position),t₀)]
      (fun p => (v (ε₀ • p)-v 0)/(ε₀:ℂ)))
    (heq₁ : (fun p => a₁ p+‖p.1‖ • b₁ p) =ᶠ[𝓝 ((0:Position),t₁)]
      (fun p => (v (ε₁ • p)-v 0)/(ε₁:ℂ))) :
    (physicalRescaledCollisionA ε₀ (v 0) a₀ =ᶠ[𝓝 ((0:Position),tStar)]
      physicalRescaledCollisionA ε₁ (v 0) a₁) ∧
    (physicalRescaledCollisionB ε₀ b₀ =ᶠ[𝓝 ((0:Position),tStar)]
      physicalRescaledCollisionB ε₁ b₁) := by
  obtain ⟨hA₀,hB₀,hid₀⟩ := physical_collision_germ_rescale hε₀ ha₀ hb₀ heq₀
  obtain ⟨hA₁,hB₁,hid₁⟩ := physical_collision_germ_rescale hε₁ ha₁ hb₁ heq₁
  rw [hpoint₀] at hA₀ hB₀ hid₀
  rw [hpoint₁] at hA₁ hB₁ hid₁
  exact analytic_distance_decomposition_germ_unique tStar hA₀ hA₁ hB₀ hB₁
    (hid₀.trans hid₁.symm)

#print axioms physical_rescaled_collision_germ_unique
end ManyBody.S8