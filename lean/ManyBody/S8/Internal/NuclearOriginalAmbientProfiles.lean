import ManyBody.S8.NuclearDistanceAmbientCompatibility
import ManyBody.S8.Internal.EvenAmbientProfileUniqueness
/-! Literal original nuclear ambient profiles and their proved evenness.

The functions are exactly u(0)+epsilon*A_axis(q/epsilon) and B_axis(q/epsilon)
of the same actual recovered axial series. They recombine to the unchanged
S8-018 original ambient function. Their true rational nuclear axis input
depends on the selected distance only through its square, so both profiles
are even in that coordinate. Positive inverse scaling transports the actual
axis holomorphic data onto the full original distance polydisc.

Actual axial data is an explicit premise of the generic analytic bridge;
the physical ground consumer must discharge it for the same original state.
-/
set_option autoImplicit false
noncomputable section
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

def nuclearOriginalAmbientA (u : Configuration 2 → ℂ) (i : Fin 2) (ε : ℝ)
    (q : Fin 3 → ℂ) : ℂ :=
  u 0+(ε:ℂ)*nuclearAmbientDescendedA
    ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
    (nuclearDistanceRealSpectator 1) 1 ((ε:ℂ)⁻¹ • q)

def nuclearOriginalAmbientB (u : Configuration 2 → ℂ) (i : Fin 2) (ε : ℝ)
    (q : Fin 3 → ℂ) : ℂ :=
  nuclearAmbientDescendedB
    ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
    (nuclearDistanceRealSpectator 1) 1 ((ε:ℂ)⁻¹ • q)

theorem nuclearOriginalAmbient_profiles_recombine
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε : ℝ} (hε : 0<ε) (q : Fin 3 → ℂ) :
    nuclearOriginalAmbientFunction u i ε q=
      nuclearOriginalAmbientA u i ε q+q 0*nuclearOriginalAmbientB u i ε q := by
  have hc : (ε:ℂ)≠0 := by exact_mod_cast hε.ne'
  dsimp only [nuclearOriginalAmbientFunction,nuclearOriginalAmbientA,nuclearOriginalAmbientB,
    nuclearAmbientDescendedFunction]
  change u 0+(ε:ℂ)*(_+(ε:ℂ)⁻¹*q 0*_)=u 0+(ε:ℂ)*_+q 0*_
  field_simp [hc]
  ring

theorem nuclearAmbientDistanceInput_selected_even (σ : ℝ) (c : ℂ) (q : Fin 3 → ℂ) :
    nuclearAmbientDistanceInput σ (c • ambientCoordinateReflect 0 q)=
      nuclearAmbientDistanceInput σ (c • q) := by
  apply Prod.ext
  · simp [nuclearAmbientDistanceInput,nuclearDistanceAxisW,nuclearDistanceAxisZ,
      ambientCoordinateReflect,mul_neg]
  · ext j; fin_cases j <;>
      simp [nuclearAmbientDistanceInput,nuclearDistanceAxisW,nuclearDistanceAxisZ,
        ambientCoordinateReflect,mul_neg]

theorem nuclearOriginalAmbient_profiles_even
    (u : Configuration 2 → ℂ) (i : Fin 2) (ε : ℝ) (q : Fin 3 → ℂ) :
    nuclearOriginalAmbientA u i ε (ambientCoordinateReflect 0 q)=nuclearOriginalAmbientA u i ε q ∧
    nuclearOriginalAmbientB u i ε (ambientCoordinateReflect 0 q)=nuclearOriginalAmbientB u i ε q := by
  constructor <;>
    simp only [nuclearOriginalAmbientA,nuclearOriginalAmbientB,nuclearAmbientDescendedA,
      nuclearAmbientDescendedB,nuclearAmbientDistanceInput_selected_even]

theorem nuclear_inverse_distance_polydisc {ε δ : ℝ} (hε : 0<ε) (q : Fin 3 → ℂ)
    (hq : q∈nuclearOriginalDistancePolydisc ε δ) :
    ‖((ε:ℂ)⁻¹ • q) 0‖<δ ∧ ‖((ε:ℂ)⁻¹ • q) 1-1‖<δ ∧ ‖((ε:ℂ)⁻¹ • q) 2-1‖<δ := by
  have hc : (ε:ℂ)≠0 := by exact_mod_cast hε.ne'
  have hn : ‖(ε:ℂ)⁻¹‖=ε⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  have h1 : ((ε:ℂ)⁻¹ • q) 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ)) := by
    change (ε:ℂ)⁻¹*q 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ)); field_simp [hc]
  have h2 : ((ε:ℂ)⁻¹ • q) 2-1=(ε:ℂ)⁻¹*(q 2-(ε:ℂ)) := by
    change (ε:ℂ)⁻¹*q 2-1=(ε:ℂ)⁻¹*(q 2-(ε:ℂ)); field_simp [hc]
  refine ⟨?_,?_,?_⟩
  · change ‖(ε:ℂ)⁻¹*q 0‖<δ
    rw [norm_mul,hn]; exact (inv_mul_lt_iff₀ hε).mpr hq.1
  · rw [h1,norm_mul,hn]; exact (inv_mul_lt_iff₀ hε).mpr hq.2.1
  · rw [h2,norm_mul,hn]; exact (inv_mul_lt_iff₀ hε).mpr hq.2.2

theorem nuclearOriginalAmbient_profiles_analytic
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A)) :
    AnalyticOnNhd ℂ (nuclearOriginalAmbientA u i ε)
      (nuclearOriginalDistancePolydisc ε (nuclearAmbientRetainedRadius M A)) ∧
    AnalyticOnNhd ℂ (nuclearOriginalAmbientB u i ε)
      (nuclearOriginalDistancePolydisc ε (nuclearAmbientRetainedRadius M A)) := by
  have hh := physicalKSAnalyticAxisRadius_pos (M:=M) hA
  have hδσ : nuclearAmbientRetainedRadius M A≤(1:ℝ)/4 := min_le_left _ _
  have hδh : nuclearAmbientRetainedRadius M A≤physicalKSAnalyticAxisRadius M A/8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ha := nuclear_ambient_distance_composition_on_polydisc (by norm_num : 0<(1:ℝ))
    hh hδσ hδh haxis.1.1 haxis.1.2.1
  have hb := nuclear_ambient_distance_composition_on_polydisc (by norm_num : 0<(1:ℝ))
    hh hδσ hδh haxis.2.1 haxis.2.2.1
  constructor
  · intro q hq
    have hs := nuclear_inverse_distance_polydisc hε q hq
    have hlin : AnalyticAt ℂ (fun q : Fin 3 → ℂ => (ε:ℂ)⁻¹ • q) q :=
      (analyticAt_const : AnalyticAt ℂ (fun _ : Fin 3 → ℂ => (ε:ℂ)⁻¹) q).smul analyticAt_id
    have hcomp := (ha.1 _ hs).comp hlin
    exact analyticAt_const.add (analyticAt_const.mul hcomp)
  · intro q hq
    have hs := nuclear_inverse_distance_polydisc hε q hq
    have hlin : AnalyticAt ℂ (fun q : Fin 3 → ℂ => (ε:ℂ)⁻¹ • q) q :=
      (analyticAt_const : AnalyticAt ℂ (fun _ : Fin 3 → ℂ => (ε:ℂ)⁻¹) q).smul analyticAt_id
    exact (hb.1 _ hs).comp hlin

#print axioms nuclearOriginalAmbient_profiles_recombine
#print axioms nuclearOriginalAmbient_profiles_even
#print axioms nuclearOriginalAmbient_profiles_analytic
theorem nuclearOriginalAmbient_profiles_bounds
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A)) :
    ∀ q∈nuclearOriginalDistancePolydisc ε (nuclearAmbientRetainedRadius M A),
      ‖nuclearOriginalAmbientA u i ε q-u 0‖≤ε*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
      ‖nuclearOriginalAmbientB u i ε q‖≤
        (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
      ‖nuclearOriginalAmbientA u i ε q‖≤‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W) := by
  have hh := physicalKSAnalyticAxisRadius_pos (M:=M) hA
  have hδσ : nuclearAmbientRetainedRadius M A≤(1:ℝ)/4 := min_le_left _ _
  have hδh : nuclearAmbientRetainedRadius M A≤physicalKSAnalyticAxisRadius M A/8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ha := nuclear_ambient_distance_composition_on_polydisc (by norm_num : 0<(1:ℝ))
    hh hδσ hδh haxis.1.1 haxis.1.2.1
  have hb := nuclear_ambient_distance_composition_on_polydisc (by norm_num : 0<(1:ℝ))
    hh hδσ hδh haxis.2.1 haxis.2.2.1
  intro q hq
  obtain ⟨hr,hs,ht⟩ := nuclear_inverse_distance_polydisc hε q hq
  have hba := ha.2 _ hr hs ht
  have hbb := hb.2 _ hr hs ht
  have hcenter : ‖nuclearOriginalAmbientA u i ε q-u 0‖≤
      ε*(16*physicalKSPointwiseAmplitude M A F0 W) := by
    dsimp only [nuclearOriginalAmbientA]
    rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left hba hε.le
  refine ⟨hcenter,hbb,?_⟩
  calc
    _=‖u 0+(nuclearOriginalAmbientA u i ε q-u 0)‖ := by congr 1; ring
    _≤‖u 0‖+‖nuclearOriginalAmbientA u i ε q-u 0‖ := norm_add_le _ _
    _≤_ := add_le_add (le_refl _) hcenter

#print axioms nuclearOriginalAmbient_profiles_bounds
end ManyBody.S8