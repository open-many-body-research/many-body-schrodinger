import NuclearDistanceAxisMap_v1
import Mathlib.Analysis.Analytic.Composition
/-! Literal bounded holomorphic composition in ambient nuclear distances.

The existing rational functions z=(r^2+s^2-u^2)/(2s) and w=r^2-z^2
feed the exact SO(2)-descended input (w,[z,s-sigma]). On a full complex
polydisc around (0,sigma,sigma), the existing 4*delta and17*delta^2 bounds
place this input in the advertised anisotropic holomorphic domain.
No square-root or transverse-area division appears in this analytic map.

These analytic composition theorems take the displayed analyticity and
bound of the function G as premises. A concrete physical consumer must
supply the literal recovered axial functions and their true real identity.
-/
noncomputable section
namespace ManyBody.S8
open TheoremT.Continuum

def nuclearAmbientDistanceInput (σ : ℝ) (q : Fin 3 → ℂ) : ℂ × (Fin 2 → ℂ) :=
  (nuclearDistanceAxisW q,![nuclearDistanceAxisZ q,q 1-(σ:ℂ)])

theorem nuclearAmbientDistanceInput_analyticAt (σ : ℝ) (q : Fin 3 → ℂ)
    (hq : q 1 ≠ 0) : AnalyticAt ℂ (nuclearAmbientDistanceInput σ) q := by
  apply AnalyticAt.prod (nuclearDistanceAxisW_analyticAt q hq)
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact nuclearDistanceAxisZ_analyticAt q hq
  · exact ((ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q).sub analyticAt_const

theorem nuclearAmbientDistanceInput_center (σ : ℝ) :
    nuclearAmbientDistanceInput σ ![0,(σ:ℂ),(σ:ℂ)]=0 := by
  apply Prod.ext
  · simp [nuclearAmbientDistanceInput,nuclearDistanceAxisW,nuclearDistanceAxisZ]
  · ext i
    fin_cases i <;> simp [nuclearAmbientDistanceInput,nuclearDistanceAxisZ]

theorem nuclearAmbientDistanceInput_domain {σ δ h : ℝ} (hσ : 0<σ) (hh : 0<h)
    (hδσ : δ≤σ/4) (hδh : δ≤h/8) (q : Fin 3 → ℂ)
    (hr : ‖q 0‖<δ) (hs : ‖q 1-(σ:ℂ)‖<δ) (hu : ‖q 2-(σ:ℂ)‖<δ) :
    q 1 ≠ 0 ∧ ‖(nuclearAmbientDistanceInput σ q).1‖<h^2 ∧
      ‖(nuclearAmbientDistanceInput σ q).2‖<h := by
  obtain ⟨hne,hz,hw⟩ := nuclearDistanceAxis_bounds hσ hδσ q hr hs hu
  have hδ : 0≤δ := (norm_nonneg _).trans hr.le
  have hsq : δ^2≤(h/8)^2 := (sq_le_sq₀ hδ (by positivity)).mpr hδh
  refine ⟨hne,hw.trans_lt (by nlinarith [sq_pos_of_pos hh]),?_⟩
  apply (pi_norm_lt_iff hh).mpr
  intro i
  fin_cases i
  · exact hz.trans_lt (by linarith)
  · exact hs.trans_le (by linarith)

theorem nuclear_ambient_distance_composition_analytic_germ
    {G : (ℂ × (Fin 2 → ℂ)) → ℂ} {σ : ℝ}
    (hσ : 0<σ) (hG : AnalyticAt ℂ G 0) :
    AnalyticAt ℂ (G ∘ nuclearAmbientDistanceInput σ) ![0,(σ:ℂ),(σ:ℂ)] := by
  have hq : (![0,(σ:ℂ),(σ:ℂ)] : Fin 3 → ℂ) 1 ≠ 0 := by
    simpa using (show (σ:ℂ)≠0 by exact_mod_cast hσ.ne')
  apply AnalyticAt.comp (f := nuclearAmbientDistanceInput σ) (g := G) _
    (nuclearAmbientDistanceInput_analyticAt σ _ hq)
  simpa only [nuclearAmbientDistanceInput_center] using hG

theorem nuclear_ambient_distance_composition_on_polydisc
    {G : (ℂ × (Fin 2 → ℂ)) → ℂ} {σ δ h M : ℝ}
    (hσ : 0<σ) (hh : 0<h) (hδσ : δ≤σ/4) (hδh : δ≤h/8)
    (hG : AnalyticOnNhd ℂ G {z | ‖z.1‖<h^2 ∧ ‖z.2‖<h})
    (hbound : ∀ w s, ‖w‖<h^2 → ‖s‖<h → ‖G (w,s)‖≤M) :
    AnalyticOnNhd ℂ (G ∘ nuclearAmbientDistanceInput σ)
      {q | ‖q 0‖<δ ∧ ‖q 1-(σ:ℂ)‖<δ ∧ ‖q 2-(σ:ℂ)‖<δ} ∧
    ∀ q, ‖q 0‖<δ → ‖q 1-(σ:ℂ)‖<δ → ‖q 2-(σ:ℂ)‖<δ →
      ‖G (nuclearAmbientDistanceInput σ q)‖≤M := by
  constructor
  · intro q hq
    obtain ⟨hne,hw,hs⟩ := nuclearAmbientDistanceInput_domain hσ hh hδσ hδh q hq.1 hq.2.1 hq.2.2
    exact AnalyticAt.comp (f := nuclearAmbientDistanceInput σ) (g := G)
      (hG _ ⟨hw,hs⟩) (nuclearAmbientDistanceInput_analyticAt σ q hne)
  · intro q hr hs hu
    obtain ⟨hne,hw,hs⟩ := nuclearAmbientDistanceInput_domain hσ hh hδσ hδh q hr hs hu
    exact hbound _ _ hw hs

#print axioms nuclearAmbientDistanceInput_domain
#print axioms nuclear_ambient_distance_composition_analytic_germ
#print axioms nuclear_ambient_distance_composition_on_polydisc
end ManyBody.S8