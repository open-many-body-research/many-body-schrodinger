import ManyBody.S8.Internal.PhysicalDistanceWeakH2
import ManyBody.S8.Internal.RealDistanceProfileExtension
import Mathlib.Tactic
/-! Local analytic distance profiles yield genuine compact physical weak H2 pullbacks across collisions. A proved smooth compact extension identifies all actual profile jets as germs at every limit image of the cutoff support. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_cutoff_distance_jets_profile_germ_congr
    {χ : Configuration 2 → ℝ} {g G : (Fin 3 → ℝ) → ℂ}
    (heq : ∀x∈tsupport χ,G=ᶠ[𝓝 (physicalDistanceTriple x)]g)
    (x v w : Configuration 2) :
    physicalCutoffDistanceValue χ G x=physicalCutoffDistanceValue χ g x ∧
    physicalCutoffDistanceFirst χ G x v=physicalCutoffDistanceFirst χ g x v ∧
    physicalCutoffDistanceSecond χ G x v w=physicalCutoffDistanceSecond χ g x v w := by
  by_cases hx : x∈tsupport χ
  · have hq := heq x hx
    have h0 := hq.eq_of_nhds
    have h1 : fderiv ℝ G (physicalDistanceTriple x)=fderiv ℝ g (physicalDistanceTriple x) := hq.fderiv_eq
    have h2 : fderiv ℝ (fderiv ℝ G) (physicalDistanceTriple x)=
      fderiv ℝ (fderiv ℝ g) (physicalDistanceTriple x) := (hq.fderiv (𝕜:=ℝ)).fderiv_eq
    simp only [physicalCutoffDistanceValue,physicalCutoffDistanceFirst,physicalCutoffDistanceSecond,
      physicalDistanceCompositionFirst,physicalDistanceCompositionSecond,h0,h1,h2,and_self]
  · obtain ⟨h0,hv,hw,hvw⟩ := cutoff_directional_jets_zero_off_tsupport hx v w
    simp only [physicalCutoffDistanceValue,physicalCutoffDistanceFirst,physicalCutoffDistanceSecond,
      h0,hv,hw,hvw,zero_smul,add_zero,and_self]

theorem physical_distance_weakH2_profile_germ_congr
    {χ : Configuration 2 → ℝ} {g G : (Fin 3 → ℝ) → ℂ}
    (heq : ∀x∈tsupport χ,G=ᶠ[𝓝 (physicalDistanceTriple x)]g)
    (hdata : PhysicalDistanceWeakH2Data χ G) : PhysicalDistanceWeakH2Data χ g := by
  obtain ⟨F,d,e,hF,hd,he,hw1,hw2,hH2⟩ := hdata
  refine ⟨F,d,e,hF.trans ?_,?_,?_,hw1,hw2,hH2⟩
  · exact Eventually.of_forall fun x =>
      (physical_cutoff_distance_jets_profile_germ_congr heq x 0 0).1
  · intro k
    exact (hd k).trans (Eventually.of_forall fun x =>
      (physical_cutoff_distance_jets_profile_germ_congr heq x (coordinateVector k) 0).2.1)
  · intro k j
    exact (he k j).trans (Eventually.of_forall fun x =>
      (physical_cutoff_distance_jets_profile_germ_congr heq x (coordinateVector k) (coordinateVector j)).2.2)

theorem actual_local_physical_distance_cutoff_weakH2
    {χ : Configuration 2 → ℝ} {g : (Fin 3 → ℝ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hR : 0<R)
    (hg : ContDiffOn ℝ ∞ g (ball a R))
    (hs : ∀x∈tsupport χ,physicalDistanceTriple x∈closedBall a (R/8)) :
    PhysicalDistanceWeakH2Data χ g := by
  obtain ⟨G,hG,hcG,heq⟩ := real_distance_profile_smooth_compact_extension hR hg
  exact physical_distance_weakH2_profile_germ_congr (fun x hx => heq _ (hs x hx))
    (actual_physical_distance_cutoff_weakH2 hχ hc hG)

#print axioms actual_local_physical_distance_cutoff_weakH2
end ManyBody.S8