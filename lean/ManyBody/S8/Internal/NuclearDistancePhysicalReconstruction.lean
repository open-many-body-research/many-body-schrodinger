import ManyBody.S8.Internal.NuclearDistanceAmbientComposition
import PhysicalKSAxisAnalyticDescent_v1
import NuclearDistanceRealAxisDomain_v1
/-! The literal ambient nuclear-distance function reconstructs the canonical
real physical representative on the proved original neighborhood.

The same actual recovered axial A/B sums compose with the rational map
(w,[z,s-sigma]). Their full complex polydisc bound gives a bounded
holomorphic function A+r*B. For feasible real distances, the actual physical
coordinate identity, Euclidean norm formula, real axis connection, and
SO(2) identification prove equality with the canonical real representative.
No analytic square root is introduced: the real square root appears only
in the already proved construction of a real configuration point.

The displayed physical and axial descent data remain premises in these
bridge declarations. A final physical graph/ground consumer must construct
them and prove any needed rotation orbit reconstruction separately.
-/
noncomputable section
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

def nuclearAmbientDescendedA (f : Space (Fin 3) → ℂ) (t0 : Position)
    (σ : ℝ) (q : Fin 3 → ℂ) : ℂ :=
  physicalKSAxisDescendedA f t0 (nuclearAmbientDistanceInput σ q)

def nuclearAmbientDescendedB (f : Space (Fin 3) → ℂ) (t0 : Position)
    (σ : ℝ) (q : Fin 3 → ℂ) : ℂ :=
  physicalKSAxisDescendedB f t0 (nuclearAmbientDistanceInput σ q)

def nuclearAmbientDescendedFunction (f : Space (Fin 3) → ℂ) (t0 : Position)
    (σ : ℝ) (q : Fin 3 → ℂ) : ℂ :=
  nuclearAmbientDescendedA f t0 σ q+q 0*nuclearAmbientDescendedB f t0 σ q

theorem physical_nuclear_ambient_axis_data
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W h σ δ : ℝ}
    (hdata : PhysicalKSAxisAnalyticDescentData f t0 M A F0 W h)
    (hσ : 0<σ) (hh : 0<h) (hδσ : δ≤σ/4) (hδh : δ≤h/8) :
    AnalyticOnNhd ℂ (nuclearAmbientDescendedFunction f t0 σ)
      {q | ‖q 0‖<δ ∧ ‖q 1-(σ:ℂ)‖<δ ∧ ‖q 2-(σ:ℂ)‖<δ} ∧
    ∀ q, ‖q 0‖<δ → ‖q 1-(σ:ℂ)‖<δ → ‖q 2-(σ:ℂ)‖<δ →
      ‖nuclearAmbientDescendedFunction f t0 σ q‖≤
        16*physicalKSPointwiseAmplitude M A F0 W+
          δ*((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) := by
  have ha := nuclear_ambient_distance_composition_on_polydisc hσ hh hδσ hδh
    hdata.1.1 hdata.1.2.1
  have hb := nuclear_ambient_distance_composition_on_polydisc hσ hh hδσ hδh
    hdata.2.1 hdata.2.2.1
  constructor
  · intro q hq
    exact (ha.1 q hq).add
      (((ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q).mul (hb.1 q hq))
  · intro q hr hs hu
    calc
      _ ≤ ‖nuclearAmbientDescendedA f t0 σ q‖+‖q 0*nuclearAmbientDescendedB f t0 σ q‖ := norm_add_le _ _
      _ = ‖nuclearAmbientDescendedA f t0 σ q‖+‖q 0‖*‖nuclearAmbientDescendedB f t0 σ q‖ := by rw [norm_mul]
      _ ≤ 16*physicalKSPointwiseAmplitude M A F0 W+
          δ*((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) :=
        add_le_add (ha.2 q hr hs hu)
          (mul_le_mul hr.le (hb.2 q hr hs hu) (norm_nonneg _) ((norm_nonneg _).trans hr.le))

theorem nuclearAmbientDistanceInput_real (σ r s u : ℝ) :
    nuclearAmbientDistanceInput σ ![(r:ℂ),(s:ℂ),(u:ℂ)] =
      ((nuclearDistanceRealW r s u:ℂ),
        ![(nuclearDistanceRealZ r s u:ℂ),((s-σ:ℝ):ℂ)]) := by
  apply Prod.ext
  · exact nuclearDistanceRealW_complexification r s u
  · ext i
    fin_cases i
    · exact nuclearDistanceRealZ_complexification r s u
    · simp [nuclearAmbientDistanceInput]

theorem physical_nuclear_ambient_canonical_identity
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {M A F0 W h σ r s u : ℝ}
    (hphysical : PhysicalKSBoxAnalyticDescentData f v (nuclearDistanceRealSpectator σ) M A F0 W)
    (haxis : PhysicalKSAxisAnalyticDescentData f (nuclearDistanceRealSpectator σ) M A F0 W h)
    (hr : 0≤r) (hw : 0≤nuclearDistanceRealW r s u) (hh : 0<h)
    (hX : r < min ((min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹)^2)
      (32*(7*physicalKSPointwiseRate M A)^2)⁻¹)
    (hT : |s-σ| < min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹)
    (hrh : r<h) (hsh : |s-σ|<h) :
    v (nuclearDistanceRealSpatial r s u) (nuclearDistanceRealSpectator s) =
      nuclearAmbientDescendedFunction f (nuclearDistanceRealSpectator σ) σ ![(r:ℂ),(s:ℂ),(u:ℂ)] := by
  obtain ⟨ρ,hρ,he,hid⟩ := hphysical.2.2.2
  have hnorm := nuclearDistanceRealSpatial_norm hr hw
  have hx : ‖nuclearDistanceRealSpatial r s u‖ < min ((ρ:ℝ)^2)
      (32*(7*physicalKSPointwiseRate M A)^2)⁻¹ := by rw [hnorm,he]; exact hX
  have ht : ‖nuclearDistanceRealSpectator s-nuclearDistanceRealSpectator σ‖ < (ρ:ℝ) := by
    rw [nuclearDistanceRealSpectator_sub_norm,he]
    exact hT
  have hp := hid (nuclearDistanceRealSpatial r s u)
    (nuclearDistanceRealSpectator s-nuclearDistanceRealSpectator σ) hx ht
  rw [add_sub_cancel,hnorm] at hp
  rw [← nuclearDistanceRealAxisInput_complex_map] at hp
  have hdom := nuclearDistanceRealAxisInput_domain hr hw hh hrh hsh
  have ha := haxis.1.2.2 (nuclearDistanceRealAxisInput σ r s u) hdom.1 hdom.2.1 hdom.2.2
  have hb := haxis.2.2.2 (nuclearDistanceRealAxisInput σ r s u) hdom.1 hdom.2.1 hdom.2.2
  dsimp only at ha hb
  rw [ha,hb,nuclearDistanceRealAxisInput_transverse_square hw,
    nuclearDistanceRealAxisInput_spectator] at hp
  simpa only [nuclearAmbientDescendedFunction,nuclearAmbientDescendedA,nuclearAmbientDescendedB,
    nuclearAmbientDistanceInput_real,Matrix.cons_val_zero] using hp

#print axioms physical_nuclear_ambient_axis_data
#print axioms nuclearAmbientDistanceInput_real
#print axioms physical_nuclear_ambient_canonical_identity
end ManyBody.S8