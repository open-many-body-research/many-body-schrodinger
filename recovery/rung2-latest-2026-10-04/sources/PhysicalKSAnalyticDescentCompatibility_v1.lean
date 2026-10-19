import PhysicalKSAnalyticDescentSurjectivity_v1
import PhysicalKSAnalyticDescentRealSlice_v1
import AnalyticNormPairUniqueness_v1

/-! Compatibility of the actual analytic-plus-distance coefficients at two
spectator centers. Equality is on the common collision-centered spatial
ball and overlapping physical spectator neighborhoods. -/
noncomputable section
set_option autoImplicit false
open Metric
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSPhysicalSpectatorRadius (M A : ℝ) : ℝ :=
  min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹

def physicalKSPhysicalSpatialRadius (M A : ℝ) : ℝ :=
  min ((physicalKSPhysicalSpectatorRadius M A)^2) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹

theorem physicalKSPhysicalSpectatorRadius_pos {M A : ℝ} (hA : 1≤A) :
    0<physicalKSPhysicalSpectatorRadius M A := by
  have hS := mul_pos (show (0:ℝ)<7 by norm_num) (physicalKSPointwiseRate_pos (M := M) hA)
  exact lt_min (by norm_num) (inv_pos.mpr hS)

theorem physicalKSPhysicalSpatialRadius_pos {M A : ℝ} (hA : 1≤A) :
    0<physicalKSPhysicalSpatialRadius M A := by
  have hr := physicalKSPhysicalSpectatorRadius_pos (M := M) hA
  have hS := mul_pos (show (0:ℝ)<7 by norm_num) (physicalKSPointwiseRate_pos (M := M) hA)
  unfold physicalKSPhysicalSpatialRadius
  positivity

theorem physicalKSAnalyticDescent_same_function_compatible
    {f0 f1 : Space (Fin 3) → ℂ} {g : Position → Position → ℂ}
    {t0 t1 : Position} {M A : ℝ} (hA : 1≤A)
    (h0 : PhysicalKSAnalyticDescentOnPhysicalNeighborhood f0 g t0 M A)
    (h1 : PhysicalKSAnalyticDescentOnPhysicalNeighborhood f1 g t1 M A)
    (ha0 : ∀ T : Position, (7*physicalKSPointwiseRate M A)*‖T‖<1 →
      AnalyticOnNhd ℝ (fun X : Position => physicalKSAnalyticDescentA f0 t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
        (ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹) ∧
      AnalyticOnNhd ℝ (fun X : Position => physicalKSAnalyticDescentB f0 t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
        (ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹))
    (ha1 : ∀ T : Position, (7*physicalKSPointwiseRate M A)*‖T‖<1 →
      AnalyticOnNhd ℝ (fun X : Position => physicalKSAnalyticDescentA f1 t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
        (ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹) ∧
      AnalyticOnNhd ℝ (fun X : Position => physicalKSAnalyticDescentB f1 t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => (T j : ℂ))))
        (ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹))
    (T : Position) (hT0 : ‖T-t0‖<physicalKSPhysicalSpectatorRadius M A)
    (hT1 : ‖T-t1‖<physicalKSPhysicalSpectatorRadius M A)
    (X : Position) (hX : ‖X‖<physicalKSPhysicalSpatialRadius M A) :
    physicalKSAnalyticDescentA f0 t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t0) j : ℂ))) =
      physicalKSAnalyticDescentA f1 t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t1) j : ℂ))) ∧
    physicalKSAnalyticDescentB f0 t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t0) j : ℂ))) =
      physicalKSAnalyticDescentB f1 t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t1) j : ℂ))) := by
  have hS : 0<7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hs (U : Position) (hU : ‖U‖<physicalKSPhysicalSpectatorRadius M A) :
      (7*physicalKSPointwiseRate M A)*‖U‖<1 := by
    have hu := hU.trans_le (min_le_right (1/1024) (7*physicalKSPointwiseRate M A)⁻¹)
    calc
      _ < (7*physicalKSPointwiseRate M A)*(7*physicalKSPointwiseRate M A)⁻¹ :=
        mul_lt_mul_of_pos_left hu hS
      _ = 1 := mul_inv_cancel₀ hS.ne'
  have ha := ha0 (T-t0) (hs _ hT0)
  have hb := ha1 (T-t1) (hs _ hT1)
  have hsub : ball (0 : Position) (physicalKSPhysicalSpatialRadius M A) ⊆
      ball (0 : Position) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹ :=
    ball_subset_ball (min_le_right _ _)
  obtain ⟨r0,hr0,he0,hid0⟩ := h0
  obtain ⟨r1,hr1,he1,hid1⟩ := h1
  rw [he0] at hid0
  rw [he1] at hid1
  have heq := analytic_norm_pair_unique (physicalKSPhysicalSpatialRadius_pos hA)
    (ha.1.mono hsub) (ha.2.mono hsub) (hb.1.mono hsub) (hb.2.mono hsub)
    (fun Y hY => by
      have hn : ‖Y‖<physicalKSPhysicalSpatialRadius M A := by
        simpa only [mem_ball,dist_zero_right] using hY
      have hleft := hid0 Y (T-t0) hn hT0
      have hright := hid1 Y (T-t1) hn hT1
      rw [show t0+(T-t0)=T by abel] at hleft
      rw [show t1+(T-t1)=T by abel] at hright
      simpa only [Complex.real_smul] using hleft.symm.trans hright)
  have hx : X ∈ ball (0 : Position) (physicalKSPhysicalSpatialRadius M A) := by
    simpa only [mem_ball,dist_zero_right] using hX
  exact ⟨heq.1 hx,heq.2 hx⟩

theorem nuclearKSPhysicalAnalyticDescent_compatible_centers
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 t1 : Position} {M A F0 W : ℝ}
    (hdata0 : PhysicalKSBoxPointwiseData ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hdata1 : PhysicalKSBoxPointwiseData ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t1 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (T : Position) (hT0 : ‖T-t0‖<physicalKSPhysicalSpectatorRadius M A)
    (hT1 : ‖T-t1‖<physicalKSPhysicalSpectatorRadius M A)
    (X : Position) (hX : ‖X‖<physicalKSPhysicalSpatialRadius M A) :
    physicalKSAnalyticDescentA ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t0) j : ℂ))) =
      physicalKSAnalyticDescentA ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t1) j : ℂ))) ∧
    physicalKSAnalyticDescentB ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t0) j : ℂ))) =
      physicalKSAnalyticDescentB ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t1) j : ℂ))) := by
  exact physicalKSAnalyticDescent_same_function_compatible hA
    (nuclearKSPhysicalAnalyticDescent_physical_neighborhood g i hdata0 hA hF0)
    (nuclearKSPhysicalAnalyticDescent_physical_neighborhood g i hdata1 hA hF0)
    (nuclearKSPhysicalAnalyticDescent_real_position_slices g i hdata0 hA hF0)
    (nuclearKSPhysicalAnalyticDescent_real_position_slices g i hdata1 hA hF0)
    T hT0 hT1 X hX

theorem pairKSPhysicalAnalyticDescent_compatible_centers
    (g : Configuration 2 → ℂ) {t0 t1 : Position} {M A F0 W : ℝ}
    (hdata0 : PhysicalKSBoxPointwiseData ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hdata1 : PhysicalKSBoxPointwiseData ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t1 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (T : Position) (hT0 : ‖T-t0‖<physicalKSPhysicalSpectatorRadius M A)
    (hT1 : ‖T-t1‖<physicalKSPhysicalSpectatorRadius M A)
    (X : Position) (hX : ‖X‖<physicalKSPhysicalSpatialRadius M A) :
    physicalKSAnalyticDescentA ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t0) j : ℂ))) =
      physicalKSAnalyticDescentA ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t1) j : ℂ))) ∧
    physicalKSAnalyticDescentB ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t0) j : ℂ))) =
      physicalKSAnalyticDescentB ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t1
        (Sum.elim (fun j => (X j : ℂ)) (fun j => ((T-t1) j : ℂ))) := by
  exact physicalKSAnalyticDescent_same_function_compatible hA
    (pairKSPhysicalAnalyticDescent_physical_neighborhood g hdata0 hA hF0)
    (pairKSPhysicalAnalyticDescent_physical_neighborhood g hdata1 hA hF0)
    (pairKSPhysicalAnalyticDescent_real_position_slices g hdata0 hA hF0)
    (pairKSPhysicalAnalyticDescent_real_position_slices g hdata1 hA hF0)
    T hT0 hT1 X hX

end TheoremT.Continuum
